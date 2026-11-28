/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorIsoIdOfGenerators
import Categorification.WeightedKLR.RedStrands.CyclotomicProjection
import Categorification.KLR.CyclotomicSplit

set_option backward.isDefEq.respectTransparency false

/-!
# Endofunctors of `D(T^λ)` fixing the vacuum, for one red strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 7.22, step (b), in the reduced case `λ₁ = λ₂ = ∅` (one red strand, `T^λ ≅ R^λ` by
Theorem 4.20, `SingleRed.cyclotomicEquiv`). Right `T^λ_ν`-modules are left modules over
`(T^λ_ν)ᵐᵒᵖ`. The idempotents `e(𝐢)` with the red strand on the left
(`SingleRed.redFirstIdem`, the images of the KLR idempotents under `SingleRed.insertRed`) form a
complete family of orthogonal idempotents, and `T^λ_ν` is generated as a ring by the scalars and
the images of the KLR idempotents, dots and crossings (`SingleRed.closure_redFirstGenerators`).

`SingleRed.derivedTensorIsoIdOfVacuum` is the resulting form of Webster's "any choice of
isomorphism `S P_∅ ≅ P_∅` induces isomorphisms between functors": an additive endofunctor `S'`
of `D(Mod T^λ_ν)` presented as a derived tensor product (`cS`), with `Φ ⋙ S' ≅ Φ` for an additive
functor `Φ` (the vacuum functor out of the category of projectives, with `p 𝐢 = F_𝐢 P_∅`), is
isomorphic to the identity, provided

* `κ`: `Φ(F_𝐢 P_∅) ≅ e(𝐢) T^λ_ν` in degree `0`;
* `hgen`: every generator acts as in the image of `Φ`, i.e. for all `𝐢, 𝐣` the left
  multiplication `e(𝐢) T^λ → e(𝐣) T^λ`, `y ↦ e(𝐣) c y`, by a scalar, an idempotent, a dot or a
  crossing `c` comes from a morphism `F_𝐢 P_∅ ⟶ F_𝐣 P_∅` (Webster's fullness
  `Hom(F_𝐢 P_∅, F_𝐣 P_∅) ↠ e(𝐣) T^λ e(𝐢)`, which is how the cyclotomic quotient acts).

`κ`, `hgen` and `cS` are the inputs still to be supplied from the derived action
(`Stendhal.blackPresCL`) and from the presentation of the S-move as a derived tensor product.
-/

open CategoryTheory CategoryTheory.Limits MulOpposite

noncomputable section

namespace Categorification.Stendhal.SingleRed

open KLR KLRAlgebra

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin 1 → I →₀ ℕ) (ν : Multiset I)

set_option hygiene false in
local notation "T" => TensorProductAlgebra k Q Λ ν

/-- **The idempotent `e(𝐢)` with the red strand on the left**, in `(T^λ_ν)ᵐᵒᵖ`. -/
def redFirstIdem (s : Seq ν) : Tᵐᵒᵖ := op (insertRed Q Λ ν (KLRAlgebra.e s))

theorem redFirstIdem_isIdempotentElem (s : Seq ν) : IsIdempotentElem (redFirstIdem Q Λ ν s) := by
  change op _ * op _ = op _
  rw [← op_mul, ← map_mul, e_mul_self]

theorem redFirstIdem_mul_of_ne {s t : Seq ν} (h : s ≠ t) :
    redFirstIdem Q Λ ν s * redFirstIdem Q Λ ν t = 0 := by
  change op _ * op _ = 0
  rw [← op_mul, ← map_mul, e_mul_e, ite_eq_right_iff.mpr (fun h' => absurd h'.symm h), map_zero,
    MulOpposite.op_zero]

theorem sum_redFirstIdem : ∑ s, redFirstIdem Q Λ ν s = 1 := by
  change ∑ s, MulOpposite.opAddEquiv (insertRed Q Λ ν (KLRAlgebra.e s)) = 1
  rw [← map_sum, ← map_sum, sum_e, map_one]
  rfl

/-- **The generators of `(T^λ_ν)ᵐᵒᵖ`**: the scalars and the images of the KLR idempotents, dots
and crossings. -/
def redFirstGenerators : Set Tᵐᵒᵖ :=
  Set.range (fun r : k => op (algebraMap k T r)) ∪
    Set.range (fun s : Seq ν => op (insertRed Q Λ ν (KLRAlgebra.e s))) ∪
    Set.range (fun a => op (insertRed Q Λ ν (KLRAlgebra.x a))) ∪
    Set.range (fun j : ℕ => op (insertRed Q Λ ν (KLRAlgebra.ψ j)))

theorem closure_redFirstGenerators : Subring.closure (redFirstGenerators Q Λ ν) = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  obtain ⟨w, hw⟩ := insertRed_surjective Q Λ ν y.unop
  rw [← op_unop y, ← hw]
  clear hw
  induction w using KLRAlgebra.klr_induction with
  | hadd u v hu hv => rw [map_add, MulOpposite.op_add]; exact add_mem hu hv
  | hmul u v hu hv => rw [map_mul, MulOpposite.op_mul]; exact mul_mem hv hu
  | hr r =>
    rw [AlgHom.commutes]
    exact Subring.subset_closure (Or.inl (Or.inl (Or.inl ⟨r, rfl⟩)))
  | he s => exact Subring.subset_closure (Or.inl (Or.inl (Or.inr ⟨s, rfl⟩)))
  | hx a => exact Subring.subset_closure (Or.inl (Or.inr ⟨a, rfl⟩))
  | hψ j => exact Subring.subset_closure (Or.inr ⟨j, rfl⟩)

section Derived

open DG.DegreeZero
open scoped DG.DegreeZero

attribute [local instance] tensorFunctorSignCommShift homotopyTensorFunctorSignCommShift

variable [DG.HasDerivedCategory.{0, 0} Tᵐᵒᵖ] [HasDerivedCategory.{0} (ModuleCat.{0} Tᵐᵒᵖ)]
  {X : Type} [AddCommGroup X] [DG.DGAddCommGroup X] [Module Tᵐᵒᵖ X] [Module Tᵐᵒᵖᵐᵒᵖ X]
  [DG.DGBimodule Tᵐᵒᵖ Tᵐᵒᵖ X]

set_option hygiene false in
local notation "𝒟" => DerivedCategory (ModuleCat.{0} Tᵐᵒᵖ)

/-- **Webster, arXiv:1309.3796v3, proof of Proposition 7.22 (b), one red strand**: an additive
endofunctor `S'` of `D(Mod T^λ_ν)` (right modules) presented as a derived tensor product with a
dg bimodule `X` (`cS`), with `Φ ⋙ S' ≅ Φ` for an additive functor `Φ : 𝒫 ⥤ D(Mod T^λ_ν)`, objects
`p 𝐢` with `Φ(p 𝐢) ≅ e(𝐢) T^λ_ν` (`κ`), and such that the left multiplications by the scalars,
idempotents, dots and crossings between the `e(𝐢) T^λ_ν` come from morphisms of `𝒫` (`hgen`),
is isomorphic to the identity.

For the vacuum functor out of `Ř^λ-pmod` (`Stendhal.blackVacuumFunctor`, `p 𝐢 = F_𝐢 P_∅`),
`εΦ` is to come from `Stendhal.blackVacuumImageIsoSelf` at the weight space of `ν`, evaluated
at the block `ν`, for a strongly equivariant `σ` acting blockwise with block component `S'`;
`κ` and `hgen` say that the derived action on `F_𝐢 T^λ_∅` is the regular action of the
cyclotomic quotient, and `cS` that the S-move is a derived tensor product. These are the
remaining inputs. -/
def derivedTensorIsoIdOfVacuum (S' : 𝒟 ⥤ 𝒟) [S'.Additive]
    (cS : dgDerivedTensor.{0} Tᵐᵒᵖ Tᵐᵒᵖ X ⋙ derivedComparison Tᵐᵒᵖ ≅
      derivedComparison Tᵐᵒᵖ ⋙ S')
    {P : Type*} [Category P] [Preadditive P] (Φ : P ⥤ 𝒟) [Φ.Additive] (εΦ : Φ ⋙ S' ≅ Φ)
    (p : Seq ν → P)
    (κ : ∀ s, Φ.obj (p s) ≅ (DerivedCategory.singleFunctor (ModuleCat.{0} Tᵐᵒᵖ) 0).obj
      (ModuleCat.of Tᵐᵒᵖ (idemLeftIdeal (redFirstIdem Q Λ ν s))))
    (hgen : redFirstGenerators Q Λ ν ⊆ hitSubring (redFirstIdem Q Λ ν)
      (redFirstIdem_isIdempotentElem Q Λ ν) (fun _ _ h => redFirstIdem_mul_of_ne Q Λ ν h)
      (sum_redFirstIdem Q Λ ν) Φ p κ) :
    S' ≅ 𝟭 _ :=
  derivedTensorIsoIdOfGenerators (redFirstIdem Q Λ ν) (redFirstIdem_isIdempotentElem Q Λ ν)
    (fun _ _ h => redFirstIdem_mul_of_ne Q Λ ν h) (sum_redFirstIdem Q Λ ν) S' cS Φ εΦ p κ
    (closure_redFirstGenerators Q Λ ν) hgen

end Derived

end Categorification.Stendhal.SingleRed
