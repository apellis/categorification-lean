/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Induction.Monoidal
import Categorification.Algebra.InductionAlongAssoc

/-!
# Monoidality of induction and comonoidality of restriction for weighted KLR algebras

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4, Proposition
2.18: induction `Ind M ⊠ N = W_{ν'+ν''} ⊗_{W_{ν'} ⊗ W_{ν''}} (M ⊠ N)` makes `⊕_ν W^ϑ_ν`-modules a
monoidal category, and restriction is coassociative. This file gives the module isomorphisms,
from the associativity and unit of Webster's map `ι` (`Monoidal.lean`) and the general results on
induction along nonunital maps (`InductionAlongAssoc.lean`).

The two sides of each isomorphism are modules over `W_{(ν₁+ν₂)+ν₃}` and `W_{ν₁+(ν₂+ν₃)}` (or
`W_{0+ν}`, `W_{ν+0}` and `W_ν`); these algebras are identified by `castW`, and the isomorphisms
are `k`-linear and semilinear along `castW`.

## Main definitions and results

* `Juxtapose.indAssocEquiv`: `Ind (Ind (M ⊠ N) ⊠ P) ≅ Ind (M ⊠ Ind (N ⊠ P))`, with
  `indAssocEquiv_smul`.
* `Juxtapose.indUnitLeftEquiv`: `Ind (W_0 ⊠ M) ≅ M`; `Juxtapose.indUnitRightEquiv`:
  `Ind (M ⊠ W_0) ≅ M`.
* `Juxtapose.resCoassocEquiv`: `(Res ⊗ id) ∘ Res ≅ (id ⊗ Res) ∘ Res`, semilinear along the
  associator of `W_{ν₁} ⊗ W_{ν₂} ⊗ W_{ν₃}`.
-/

namespace Categorification.WeightedKLR

namespace Juxtapose

open InductionAlong GalleryAlgebra
open scoped TensorProduct

universe w

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

variable (k Γ) in
/-- `ι_{ν';ν''}` is `k`-linear. -/
theorem inductionRingHom_smul (ν' ν'' : I →₀ ℕ) (r : k)
    (t : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') :
    inductionRingHom k Γ ν' ν'' (r • t) = r • inductionRingHom k Γ ν' ν'' t :=
  map_smul (inductionMap k Γ ν' ν'') r t

/-! ### Associativity of induction -/

section Assoc

variable (ν₁ ν₂ ν₃ : I →₀ ℕ) (M N P : Type w) [AddCommGroup M] [Module k M]
  [Module (WeightedKLRAlgebra k Γ ν₁) M] [IsScalarTower k (WeightedKLRAlgebra k Γ ν₁) M]
  [AddCommGroup N] [Module k N] [Module (WeightedKLRAlgebra k Γ ν₂) N]
  [IsScalarTower k (WeightedKLRAlgebra k Γ ν₂) N] [AddCommGroup P] [Module k P]
  [Module (WeightedKLRAlgebra k Γ ν₃) P] [IsScalarTower k (WeightedKLRAlgebra k Γ ν₃) P]

variable (k Γ) in
/-- **Associativity of induction** (Webster, arXiv:1209.2463v4, §2.4, Proposition 2.18):
`Ind (Ind (M ⊠ N) ⊠ P) ≅ Ind (M ⊠ Ind (N ⊠ P))`, a `k`-linear isomorphism from a
`W_{(ν₁+ν₂)+ν₃}`-module to a `W_{ν₁+(ν₂+ν₃)}`-module, semilinear along
`castW (add_assoc ν₁ ν₂ ν₃)` (`indAssocEquiv_smul`). -/
noncomputable def indAssocEquiv :
    ind k Γ (ν₁ + ν₂) ν₃ (ind k Γ ν₁ ν₂ M N) P ≃ₗ[k]
      ind k Γ ν₁ (ν₂ + ν₃) M (ind k Γ ν₂ ν₃ N P) :=
  indAssocLinear k (inductionRingHom k Γ ν₁ ν₂) (inductionRingHom_smul k Γ ν₁ ν₂)
    (inductionRingHom k Γ ν₂ ν₃) (inductionRingHom_smul k Γ ν₂ ν₃)
    (inductionRingHom k Γ (ν₁ + ν₂) ν₃) (inductionRingHom k Γ ν₁ (ν₂ + ν₃))
    (castW k Γ (add_assoc ν₁ ν₂ ν₃)) (inductionMap_assoc ν₁ ν₂ ν₃) M N P

theorem indAssocEquiv_smul (d : WeightedKLRAlgebra k Γ (ν₁ + ν₂ + ν₃))
    (x : ind k Γ (ν₁ + ν₂) ν₃ (ind k Γ ν₁ ν₂ M N) P) :
    indAssocEquiv k Γ ν₁ ν₂ ν₃ M N P (d • x) =
      castW k Γ (add_assoc ν₁ ν₂ ν₃) d • indAssocEquiv k Γ ν₁ ν₂ ν₃ M N P x :=
  indAssoc_smul k (inductionRingHom k Γ ν₁ ν₂) (inductionRingHom_smul k Γ ν₁ ν₂)
    (inductionRingHom k Γ ν₂ ν₃) (inductionRingHom_smul k Γ ν₂ ν₃)
    (inductionRingHom k Γ (ν₁ + ν₂) ν₃) (inductionRingHom k Γ ν₁ (ν₂ + ν₃))
    (castW k Γ (add_assoc ν₁ ν₂ ν₃)) (inductionMap_assoc ν₁ ν₂ ν₃) M N P d x

end Assoc

/-! ### Units of induction -/

section Unit

variable (ν : I →₀ ℕ) (M : Type w) [AddCommGroup M] [Module k M]
  [Module (WeightedKLRAlgebra k Γ ν) M] [IsScalarTower k (WeightedKLRAlgebra k Γ ν) M]

variable (k Γ) in
/-- **Left unit of induction** (Webster, arXiv:1209.2463v4, §2.4, Proposition 2.18):
`Ind (W_0 ⊠ M) ≅ M`, with `W_0` the regular module; `k`-linear and semilinear along
`castW (zero_add ν)` (`indUnitLeftEquiv_smul`). -/
noncomputable def indUnitLeftEquiv :
    ind k Γ 0 ν (WeightedKLRAlgebra k Γ 0) M ≃ₗ[k] M :=
  indUnitLeftLinear k (inductionRingHom k Γ 0 ν) (inductionRingHom_smul k Γ 0 ν)
    (castW k Γ (zero_add ν)) (inductionMap_one_tmul (Γ := Γ)) M

theorem indUnitLeftEquiv_smul (d : WeightedKLRAlgebra k Γ (0 + ν))
    (x : ind k Γ 0 ν (WeightedKLRAlgebra k Γ 0) M) :
    indUnitLeftEquiv k Γ ν M (d • x) = castW k Γ (zero_add ν) d • indUnitLeftEquiv k Γ ν M x :=
  indUnitLeft_smul k (inductionRingHom k Γ 0 ν) (inductionRingHom_smul k Γ 0 ν)
    (castW k Γ (zero_add ν)) (inductionMap_one_tmul (Γ := Γ)) M d x

variable (k Γ) in
/-- **Right unit of induction** (Webster, arXiv:1209.2463v4, §2.4, Proposition 2.18):
`Ind (M ⊠ W_0) ≅ M`, with `W_0` the regular module; `k`-linear and semilinear along
`castW (add_zero ν)` (`indUnitRightEquiv_smul`). -/
noncomputable def indUnitRightEquiv :
    ind k Γ ν 0 M (WeightedKLRAlgebra k Γ 0) ≃ₗ[k] M :=
  indUnitRightLinear k (inductionRingHom k Γ ν 0) (inductionRingHom_smul k Γ ν 0)
    (castW k Γ (add_zero ν)) (inductionMap_tmul_one (Γ := Γ)) M

theorem indUnitRightEquiv_smul (d : WeightedKLRAlgebra k Γ (ν + 0))
    (x : ind k Γ ν 0 M (WeightedKLRAlgebra k Γ 0)) :
    indUnitRightEquiv k Γ ν M (d • x) = castW k Γ (add_zero ν) d • indUnitRightEquiv k Γ ν M x :=
  indUnitRight_smul k (inductionRingHom k Γ ν 0) (inductionRingHom_smul k Γ ν 0)
    (castW k Γ (add_zero ν)) (inductionMap_tmul_one (Γ := Γ)) M d x

end Unit

/-! ### Coassociativity of restriction -/

section Coassoc

variable (ν₁ ν₂ ν₃ : I →₀ ℕ) (L L' : Type w) [AddCommGroup L]
  [Module (WeightedKLRAlgebra k Γ (ν₁ + ν₂ + ν₃)) L] [AddCommGroup L']
  [Module (WeightedKLRAlgebra k Γ (ν₁ + (ν₂ + ν₃))) L'] (e : L ≃+ L')
  (he : ∀ (d : WeightedKLRAlgebra k Γ (ν₁ + ν₂ + ν₃)) l,
    e (d • l) = castW k Γ (add_assoc ν₁ ν₂ ν₃) d • e l)

variable (k Γ) in
/-- **Coassociativity of restriction** (Webster, arXiv:1209.2463v4, §2.4, Proposition 2.18):
for a `castW`-semilinear isomorphism `e : L ≅ L'` from a `W_{(ν₁+ν₂)+ν₃}`-module to a
`W_{ν₁+(ν₂+ν₃)}`-module, `(Res_{ν₁,ν₂} ⊗ id) (Res_{ν₁+ν₂,ν₃} L) ≅ (id ⊗ Res_{ν₂,ν₃})
(Res_{ν₁,ν₂+ν₃} L')`, semilinear along the associator of `W_{ν₁} ⊗ W_{ν₂} ⊗ W_{ν₃}`
(`resCoassocEquiv_smul`). The underlying map is `e` (`val_resCoassocEquiv`). -/
noncomputable def resCoassocEquiv :
    Res (tensorLeft (A := WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) k
      (WeightedKLRAlgebra k Γ ν₃) (inductionRingHom k Γ ν₁ ν₂)
      (inductionRingHom_smul k Γ ν₁ ν₂)) (res k Γ (ν₁ + ν₂) ν₃ L) ≃+
    Res (tensorRight (A := WeightedKLRAlgebra k Γ ν₂ ⊗[k] WeightedKLRAlgebra k Γ ν₃) k
      (WeightedKLRAlgebra k Γ ν₁) (inductionRingHom k Γ ν₂ ν₃)
      (inductionRingHom_smul k Γ ν₂ ν₃)) (res k Γ ν₁ (ν₂ + ν₃) L') :=
  resCoassoc k (inductionRingHom k Γ ν₁ ν₂) (inductionRingHom_smul k Γ ν₁ ν₂)
    (inductionRingHom k Γ ν₂ ν₃) (inductionRingHom_smul k Γ ν₂ ν₃)
    (inductionRingHom k Γ (ν₁ + ν₂) ν₃) (inductionRingHom k Γ ν₁ (ν₂ + ν₃))
    (castW k Γ (add_assoc ν₁ ν₂ ν₃)) (inductionMap_assoc ν₁ ν₂ ν₃) L L' e he

theorem val_resCoassocEquiv
    (m : Res (tensorLeft (A := WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) k
      (WeightedKLRAlgebra k Γ ν₃) (inductionRingHom k Γ ν₁ ν₂)
      (inductionRingHom_smul k Γ ν₁ ν₂)) (res k Γ (ν₁ + ν₂) ν₃ L)) :
    (resCoassocEquiv k Γ ν₁ ν₂ ν₃ L L' e he m).val.val = e m.val.val := rfl

theorem resCoassocEquiv_smul
    (t : (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) ⊗[k]
      WeightedKLRAlgebra k Γ ν₃)
    (m : Res (tensorLeft (A := WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) k
      (WeightedKLRAlgebra k Γ ν₃) (inductionRingHom k Γ ν₁ ν₂)
      (inductionRingHom_smul k Γ ν₁ ν₂)) (res k Γ (ν₁ + ν₂) ν₃ L)) :
    resCoassocEquiv k Γ ν₁ ν₂ ν₃ L L' e he (t • m) =
      Algebra.TensorProduct.assoc k k k _ _ _ t • resCoassocEquiv k Γ ν₁ ν₂ ν₃ L L' e he m :=
  resCoassoc_smul k (inductionRingHom k Γ ν₁ ν₂) (inductionRingHom_smul k Γ ν₁ ν₂)
    (inductionRingHom k Γ ν₂ ν₃) (inductionRingHom_smul k Γ ν₂ ν₃)
    (inductionRingHom k Γ (ν₁ + ν₂) ν₃) (inductionRingHom k Γ ν₁ (ν₂ + ν₃))
    (castW k Γ (add_assoc ν₁ ν₂ ν₃)) (inductionMap_assoc ν₁ ν₂ ν₃) L L' e he t m

end Coassoc

end Juxtapose

end Categorification.WeightedKLR
