/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceBlockAlgebraAction
import Categorification.WeightedKLR.RedStrands.ParabolicStandardUnitExt

/-!
# Two-piece standardization is fully faithful

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 5.26, full faithfulness of standardization, for the partial standardization with
two pieces (the first `ℓ` red strands, and the last red strand with the black strands to its
right) in the induced model. For all modules `N`, `N'` over the factor algebra `D`,
`g ↦ S(g)` is a bijection `Hom_D(N, N') ≅ Hom_{T^λ}(S(N), S(N'))`
(`parabolicStandardMapT_bijective`), and in particular `End_D(N) ≅ End_{T^λ}(S(N))` as rings
(`parabolicStandardEndEquiv`).

The proof: the unit vectors `1 ⊗ n` generate `S(N)` (`parabolicStandardT_ext`) and are fixed by
the image of the identity of the parabolic subalgebra, which maps all of `S(N')` into the unit
copy of `N'` (`parabolicStandardAction_concat_mem_range`); so a `T^λ`-linear map
`f : S(N) → S(N')` sends unit vectors to unit vectors, and its restriction to them is a map
over the factor algebra inducing `f`. Webster deduces full faithfulness from the endomorphisms
of standard modules; here it is proved directly and holds for all modules over every field.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (θ β : Multiset I)
  (hQ : KLRSymm Q)

local notation "D" => parabolicFactorAlgebra Q Λ θ β
local notation "T" => TensorProductAlgebra k Q Λ (θ + β)

variable {N N' : Type*} [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]
  [AddCommGroup N'] [Module k N'] [Module (parabolicFactorAlgebra Q Λ θ β) N']
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N']

/-- Unit vectors are fixed by the image of the identity of the parabolic subalgebra. -/
theorem parabolicStandardTUnit_eq_concat_one_smul (n : N) :
    parabolicStandardTUnit Q Λ θ β hQ n =
      parabolicAffine Q Λ θ β (concat (stendhalQ Q Λ) _ _ 1) •
        parabolicStandardTUnit Q Λ θ β hQ n := by
  rw [← parabolicStandardTUnit_smul, map_one, one_smul]

/-- A `T^λ`-linear map of standardizations sends unit vectors to unit vectors. -/
theorem map_parabolicStandardTUnit_mem_range
    (f : ParabolicStandardT Q Λ θ β N hQ →ₗ[T] ParabolicStandardT Q Λ θ β N' hQ) (n : N) :
    f (parabolicStandardTUnit Q Λ θ β hQ n) ∈
      LinearMap.range (parabolicStandardUnit Q Λ θ β N') := by
  rw [parabolicStandardTUnit_eq_concat_one_smul, map_smul]
  exact parabolicStandardAction_concat_mem_range Q Λ θ β N' hQ 1 _

/-- The unit copy of `N'` in its standardization. -/
def parabolicStandardUnitEquiv :
    N' ≃ₗ[k] LinearMap.range (parabolicStandardUnit Q Λ θ β N') :=
  LinearEquiv.ofInjective _ (parabolicStandardUnit_injective Q Λ θ β N' hQ)

theorem parabolicStandardTUnit_injective :
    Function.Injective (fun n : N' => parabolicStandardTUnit Q Λ θ β hQ n) :=
  parabolicStandardUnit_injective Q Λ θ β N' hQ

/-- The restriction of a `T^λ`-linear map of standardizations to the unit vectors, as a
function. -/
def parabolicStandardRestrictFun
    (f : ParabolicStandardT Q Λ θ β N hQ →ₗ[T] ParabolicStandardT Q Λ θ β N' hQ) (n : N) : N' :=
  (parabolicStandardUnitEquiv Q Λ θ β hQ).symm
    ⟨f (parabolicStandardTUnit Q Λ θ β hQ n), map_parabolicStandardTUnit_mem_range Q Λ θ β hQ f n⟩

theorem parabolicStandardTUnit_restrictFun
    (f : ParabolicStandardT Q Λ θ β N hQ →ₗ[T] ParabolicStandardT Q Λ θ β N' hQ) (n : N) :
    parabolicStandardTUnit Q Λ θ β hQ (parabolicStandardRestrictFun Q Λ θ β hQ f n) =
      f (parabolicStandardTUnit Q Λ θ β hQ n) :=
  congrArg Subtype.val ((parabolicStandardUnitEquiv Q Λ θ β hQ).apply_symm_apply
    ⟨f (parabolicStandardTUnit Q Λ θ β hQ n), map_parabolicStandardTUnit_mem_range Q Λ θ β hQ f n⟩)

/-- The restriction of a `T^λ`-linear map of standardizations to the unit vectors, as a map of
modules over the factor algebra. -/
def parabolicStandardRestrict
    (f : ParabolicStandardT Q Λ θ β N hQ →ₗ[T] ParabolicStandardT Q Λ θ β N' hQ) :
    N →ₗ[D] N' where
  toFun := parabolicStandardRestrictFun Q Λ θ β hQ f
  map_add' n n' := parabolicStandardTUnit_injective Q Λ θ β hQ (by
    dsimp only
    rw [parabolicStandardTUnit_restrictFun, parabolicStandardTUnit_add, map_add,
      parabolicStandardTUnit_add, parabolicStandardTUnit_restrictFun,
      parabolicStandardTUnit_restrictFun])
  map_smul' d n := by
    obtain ⟨b, rfl⟩ := parabolicInputMap_surjective Q Λ θ β d
    refine parabolicStandardTUnit_injective Q Λ θ β hQ ?_
    dsimp only
    rw [RingHom.id_apply, parabolicStandardTUnit_restrictFun, parabolicStandardTUnit_smul,
      parabolicStandardTUnit_smul, map_smul, parabolicStandardTUnit_restrictFun]

theorem parabolicStandardTUnit_parabolicStandardRestrict
    (f : ParabolicStandardT Q Λ θ β N hQ →ₗ[T] ParabolicStandardT Q Λ θ β N' hQ) (n : N) :
    parabolicStandardTUnit Q Λ θ β hQ (parabolicStandardRestrict Q Λ θ β hQ f n) =
      f (parabolicStandardTUnit Q Λ θ β hQ n) :=
  parabolicStandardTUnit_restrictFun Q Λ θ β hQ f n

theorem parabolicStandardMapT_parabolicStandardRestrict
    (f : ParabolicStandardT Q Λ θ β N hQ →ₗ[T] ParabolicStandardT Q Λ θ β N' hQ) :
    parabolicStandardMapT Q Λ hQ (parabolicStandardRestrict Q Λ θ β hQ f) = f :=
  parabolicStandardT_ext Q Λ θ β hQ fun n => by
    rw [parabolicStandardMapT_unit, parabolicStandardTUnit_parabolicStandardRestrict]

theorem parabolicStandardRestrict_parabolicStandardMapT (g : N →ₗ[D] N') :
    parabolicStandardRestrict Q Λ θ β hQ (parabolicStandardMapT Q Λ hQ g) = g :=
  LinearMap.ext fun n => parabolicStandardTUnit_injective Q Λ θ β hQ <| by
    dsimp only
    rw [parabolicStandardTUnit_parabolicStandardRestrict, parabolicStandardMapT_unit]

/-- **Standardization is fully faithful** (Webster, arXiv:1309.3796v3, Proposition 5.26, for
the two-piece standardization of the induced model): `g ↦ S(g)` is a bijection
`Hom_D(N, N') → Hom_{T^λ}(S(N), S(N'))`, for all modules over the factor algebra. -/
theorem parabolicStandardMapT_bijective :
    Function.Bijective (parabolicStandardMapT Q Λ hQ (N := N) (N' := N') (θ := θ) (β := β)) :=
  Function.bijective_iff_has_inverse.2 ⟨parabolicStandardRestrict Q Λ θ β hQ,
    parabolicStandardRestrict_parabolicStandardMapT Q Λ θ β hQ,
    parabolicStandardMapT_parabolicStandardRestrict Q Λ θ β hQ⟩

variable (N) in
/-- Standardization on endomorphisms, as a ring map. -/
def parabolicStandardEndHom :
    Module.End D N →+* Module.End T (ParabolicStandardT Q Λ θ β N hQ) where
  toFun := parabolicStandardMapT Q Λ hQ
  map_one' := parabolicStandardMapT_id Q Λ hQ
  map_mul' g g' := parabolicStandardMapT_comp Q Λ hQ g' g
  map_zero' := parabolicStandardMapT_zero Q Λ hQ
  map_add' := parabolicStandardMapT_add Q Λ hQ

variable (N) in
/-- **Endomorphisms of a standardization** (Webster, arXiv:1309.3796v3, Proposition 5.26, for
the two-piece standardization of the induced model): `End_D(N) ≅ End_{T^λ}(S(N))`. -/
def parabolicStandardEndEquiv :
    Module.End D N ≃+* Module.End T (ParabolicStandardT Q Λ θ β N hQ) :=
  RingEquiv.ofBijective (parabolicStandardEndHom Q Λ θ β hQ N)
    (parabolicStandardMapT_bijective Q Λ θ β hQ)

theorem parabolicStandardEndEquiv_apply (g : Module.End D N) :
    parabolicStandardEndEquiv Q Λ θ β hQ N g = parabolicStandardMapT Q Λ hQ g :=
  rfl

end Categorification.Stendhal
