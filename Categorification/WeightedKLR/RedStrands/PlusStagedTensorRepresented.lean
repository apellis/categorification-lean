/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CutStandardTensorRepresented
import Categorification.WeightedKLR.RedStrands.SingStdTensorRepresented
import Categorification.WeightedKLR.RedStrands.PartialStandardizationPlusStaged
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSpectatorAssoc
import Categorification.WeightedKLR.RedStrands.PartialStandardizationDerived

/-!
# The partial standardization `S_+` is tensoring with a bimodule

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1 and §7.3
(proof of Lemma 7.19). The partial standardization of `λ⁺` with three blocks
(`plusStandardFunctor`) is the standardization at the inner cut, the first block carried
along (`plusMidFunctor`), followed by the standardization at the outer cut
(`cutStandardFunctor`) (`plusStandardFunctorIso`). Both are presented by a partial
standardization at a cut, so both are tensoring with a bimodule
(`CutStandardPresented.isTensorRepresented`), and so is `S_+` (`plusStagedStd`), whose other
stages are standardizations with singleton blocks (`isTensorRepresented_singStd`) and
restrictions of scalars (`isTensorRepresented_plusStagedStd`).

## Main definitions

* `Stendhal.cutStandardFunctor`: partial standardization at a cut, as a functor.
* `Stendhal.CupCap.plusMidFunctor`: the standardization at the inner cut of the three blocks.

## Main results

* `Stendhal.CupCap.plusStandardFunctorIso`.
* `Stendhal.CupCap.isTensorRepresented_plusStandardFunctor`,
  `Stendhal.CupCap.isTensorRepresented_plusStagedStd`.
-/

universe u

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra TypeA TensorRepresented
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I k : Type u} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q)

/-! ### Partial standardization at a cut, as a functor -/

section Cut

variable {a r : ℕ} (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)
  {A : Type u} [Ring A] [Algebra k A] (ψ : A →ₐ[k] TensorProductAlgebra k Q Λ (θ + β))

/-- The partial standardization at a cut of a module over `D`, as a module over `A` through
`ψ : A → T^λ(θ + β)`. -/
@[nolint unusedArguments]
def CutStandardModule (_hQ : KLRSymm Q) (_ψ : A →ₐ[k] TensorProductAlgebra k Q Λ (θ + β))
    (M : ModuleCat.{u} (cutFactorAlgebra Q Λ θ β)) : Type u :=
  CutStandard Q Λ θ β M

variable (M : ModuleCat.{u} (cutFactorAlgebra Q Λ θ β))

/-- The identity of the factor algebra of the cut. -/
def cutFactorId := cutAlgHom Q Λ θ β (AlgHom.id k (cutFactorAlgebra Q Λ θ β))

instance : AddCommGroup (CutStandardModule Q Λ θ β hQ ψ M) :=
  inferInstanceAs (AddCommGroup (CutStandard Q Λ θ β M))

instance : Module A (CutStandardModule Q Λ θ β hQ ψ M) :=
  Module.compHom (CutStandard Q Λ θ β M) ((cutStandardAction Q Λ θ β M hQ).comp ψ).toRingHom

/-- **Partial standardization at a cut, as a functor** from modules over
`T^{λ_1…λ_a}(θ) ⊗ T^{λ_{a+1}…λ_{a+r}}(β)` to modules over `A`, through
`ψ : A → T^λ(θ + β)`. -/
def cutStandardFunctor : ModuleCat.{u} (cutFactorAlgebra Q Λ θ β) ⥤ ModuleCat.{u} A where
  obj M := ModuleCat.of _ (CutStandardModule Q Λ θ β hQ ψ M)
  map g := ModuleCat.ofHom
    { toFun := cutStandardMap Q Λ θ β g.hom
      map_add' := map_add _
      map_smul' := fun t => cutStandardMap_action Q Λ θ β hQ g.hom (ψ t) }
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun z =>
    LinearMap.congr_fun (cutStandardMap_id Q Λ θ β) z)
  map_comp g g' := ModuleCat.hom_ext (LinearMap.ext fun z =>
    cutStandardMap_comp Q Λ θ β g.hom g'.hom z)

instance cutStandardFunctor_additive : (cutStandardFunctor Q hQ Λ θ β ψ).Additive where
  map_add {_ _ f g} := ModuleCat.hom_ext (LinearMap.ext fun z =>
    (cutStandardMap_add Q Λ θ β f.hom g.hom z).trans rfl)

/-- The identity of a module over `D`, onto its restriction along the identity. -/
def cutRestrIdEquiv : M ≃ₗ[cutFactorAlgebra Q Λ θ β]
    CutRestr (R := cutFactorAlgebra Q Λ θ β) Q Λ θ β (cutFactorId Q Λ θ β) M where
  toFun n := n
  invFun n := n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem cutStandardFunctor_smul_aux (c : k) (x : CutStandard Q Λ θ β M) :
    cutStandardMap Q Λ θ β (cutRestrIdEquiv Q Λ θ β M).toLinearMap
      (cutStandardAction Q Λ θ β M hQ (ψ (algebraMap k A c)) x) =
      c • cutStandardMap Q Λ θ β (cutRestrIdEquiv Q Λ θ β M).toLinearMap x := by
  rw [AlgHom.commutes, AlgHom.commutes]
  exact map_smul (cutStandardMap Q Λ θ β (cutRestrIdEquiv Q Λ θ β M).toLinearMap) c x

/-- Partial standardization at a cut is presented by itself. -/
def cutStandardFunctorPresented :
    CutStandardPresented (R := cutFactorAlgebra Q Λ θ β) Q Λ θ β (cutFactorId Q Λ θ β)
      (cutStandardFunctor Q hQ Λ θ β ψ) where
  equiv M := (cutStandardMapEquiv Q Λ θ β (cutRestrIdEquiv Q Λ θ β M)).toAddEquiv
  map {M M'} g x := by
    have h : (cutRestrIdEquiv Q Λ θ β M').toLinearMap ∘ₗ g.hom =
        cutRestrHom Q Λ θ β (cutFactorId Q Λ θ β) g.hom ∘ₗ
          (cutRestrIdEquiv Q Λ θ β M).toLinearMap := LinearMap.ext fun _ => rfl
    exact (cutStandardMap_comp Q Λ θ β g.hom (cutRestrIdEquiv Q Λ θ β M').toLinearMap
      x).symm.trans ((congrArg (fun f => cutStandardMap Q Λ θ β f x) h).trans
        (cutStandardMap_comp Q Λ θ β (cutRestrIdEquiv Q Λ θ β M).toLinearMap
          (cutRestrHom Q Λ θ β (cutFactorId Q Λ θ β) g.hom) x))
  smul M c x := cutStandardFunctor_smul_aux Q hQ Λ θ β ψ M c x

/-- **Partial standardization at a cut is tensoring with a bimodule.** -/
theorem isTensorRepresented_cutStandardFunctor :
    IsTensorRepresented (cutStandardFunctor Q hQ Λ θ β ψ) :=
  (cutStandardFunctorPresented Q hQ Λ θ β ψ).isTensorRepresented

end Cut

namespace CupCap

variable {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ) (j : ℕ) (hj : j ≤ ℓ)
  (θ β γ : Multiset I)

/-- The semiring structure of the algebra of the three blocks of `λ⁺`, through its ring
structure (so that linear maps over it elaborate). -/
private abbrev plusNonAssocSemiringT : NonAssocSemiring (PlusFactorAlgebra Q Λ Λc j hj θ β γ) :=
  Semiring.toNonAssocSemiring

attribute [local instance high] plusNonAssocSemiringT

local notation "Lt" => blocksTailLabels (plusBlockLabels Λ Λc j hj)

/-- **The standardization at the inner cut of the three blocks of `λ⁺`**, the first block
carried along: modules over `T^{λ_1…λ_j}(θ) ⊗ (T^{μ μ*}(β) ⊗ T^{λ_{j+1}…λ_ℓ}(γ))` to modules
over `T^{λ_1…λ_j}(θ) ⊗ T^{μ μ* λ_{j+1}…λ_ℓ}(β + γ)`. -/
def plusMidFunctor :
    ModuleCat.{u} (plusFactorAlgCat Q Λ Λc j hj θ β γ) ⥤
      ModuleCat.{u} (cutFactorAlgebra Q (plusBlockLabels Λ Λc j hj) θ (β + γ)) where
  obj N := ModuleCat.of _ (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ β γ
    (PlusInput Q Λ Λc j hj θ β γ (PlusWrap Q Λ Λc j hj θ β γ N)) hQ)
  map g := ModuleCat.ofHom (blocksMidHom Q (plusBlockLabels Λ Λc j hj) θ β γ hQ
    (plusInputHom Q Λ Λc j hj θ β γ (plusWrapHom Q Λ Λc j hj θ β γ g)))
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun z =>
    LinearMap.congr_fun (cutStandardMap_id Q Lt β γ) z)
  map_comp g g' := ModuleCat.hom_ext (LinearMap.ext fun z =>
    cutStandardMap_comp Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)) β γ
      (blocksInnerHom Q (plusBlockLabels Λ Λc j hj) θ β γ
        (plusInputHom Q Λ Λc j hj θ β γ (plusWrapHom Q Λ Λc j hj θ β γ g)))
      (blocksInnerHom Q (plusBlockLabels Λ Λc j hj) θ β γ
        (plusInputHom Q Λ Λc j hj θ β γ (plusWrapHom Q Λ Λc j hj θ β γ g'))) z)

instance plusMidFunctor_additive : (plusMidFunctor Q hQ Λ Λc j hj θ β γ).Additive where
  map_add {_ _ f g} := ModuleCat.hom_ext (LinearMap.ext fun z => by
    have h : blocksInnerHom Q (plusBlockLabels Λ Λc j hj) θ β γ
        (plusInputHom Q Λ Λc j hj θ β γ (plusWrapHom Q Λ Λc j hj θ β γ (f + g))) =
      blocksInnerHom Q (plusBlockLabels Λ Λc j hj) θ β γ
          (plusInputHom Q Λ Λc j hj θ β γ (plusWrapHom Q Λ Λc j hj θ β γ f)) +
        blocksInnerHom Q (plusBlockLabels Λ Λc j hj) θ β γ
          (plusInputHom Q Λ Λc j hj θ β γ (plusWrapHom Q Λ Λc j hj θ β γ g)) :=
      LinearMap.ext fun _ => rfl
    exact (congrArg (fun h => cutStandardMap Q (blocksTailLabels (plusBlockLabels Λ Λc j hj))
      β γ h z) h).trans ((cutStandardMap_add Q Lt β γ _ _ z).trans rfl))

/-- The inclusion of the last two blocks into the algebra of the three blocks of `λ⁺`. -/
def plusTailIncl :=
  cutAlgHom Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)) β γ
    (R := plusFactorAlgCat Q Λ Λc j hj θ β γ)
    ((plusFactorEquiv Q Λ Λc j hj θ β γ).toAlgHom.comp Algebra.TensorProduct.includeRight)

/-- The input of the inner standardization, as a restriction along the inclusion of the last
two blocks. -/
def plusInnerEquiv (N : ModuleCat.{u} (plusFactorAlgCat Q Λ Λc j hj θ β γ)) :
    BlocksInner Q (plusBlockLabels Λ Λc j hj) θ β γ
        (PlusInput Q Λ Λc j hj θ β γ (PlusWrap Q Λ Λc j hj θ β γ N)) ≃ₗ[cutFactorAlgebra Q
          (blocksTailLabels (plusBlockLabels Λ Λc j hj)) β γ]
      CutRestr (R := plusFactorAlgCat Q Λ Λc j hj θ β γ) Q
        (blocksTailLabels (plusBlockLabels Λ Λc j hj)) β γ (plusTailIncl Q Λ Λc j hj θ β γ) N where
  toFun n := n
  invFun n := n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem plusMid_smul_aux (N : ModuleCat.{u} (plusFactorAlgCat Q Λ Λc j hj θ β γ)) (c : k)
    (x : BlocksMid Q (plusBlockLabels Λ Λc j hj) θ β γ
      (PlusInput Q Λ Λc j hj θ β γ (PlusWrap Q Λ Λc j hj θ β γ N)) hQ) :
    cutStandardMap Q Lt β γ (plusInnerEquiv Q Λ Λc j hj θ β γ N).toLinearMap
      (blocksMidAction Q (plusBlockLabels Λ Λc j hj) θ β γ
        (PlusInput Q Λ Λc j hj θ β γ (PlusWrap Q Λ Λc j hj θ β γ N)) hQ
        (algebraMap k (cutFactorAlgebra Q (plusBlockLabels Λ Λc j hj) θ (β + γ)) c) x) =
      c • cutStandardMap Q Lt β γ (plusInnerEquiv Q Λ Λc j hj θ β γ N).toLinearMap x := by
  rw [AlgHom.commutes]
  exact map_smul (cutStandardMap Q Lt β γ (plusInnerEquiv Q Λ Λc j hj θ β γ N).toLinearMap) c x

/-- The standardization at the inner cut is presented by a partial standardization at a cut. -/
def plusMidPresented :
    CutStandardPresented (R := plusFactorAlgCat Q Λ Λc j hj θ β γ) Q
      (blocksTailLabels (plusBlockLabels Λ Λc j hj)) β γ
      (plusTailIncl Q Λ Λc j hj θ β γ) (plusMidFunctor Q hQ Λ Λc j hj θ β γ) where
  equiv N := (cutStandardMapEquiv Q Lt β γ (plusInnerEquiv Q Λ Λc j hj θ β γ N)).toAddEquiv
  map {N N'} g x := by
    have h : (plusInnerEquiv Q Λ Λc j hj θ β γ N').toLinearMap ∘ₗ
        blocksInnerHom Q (plusBlockLabels Λ Λc j hj) θ β γ
          (plusInputHom Q Λ Λc j hj θ β γ (plusWrapHom Q Λ Λc j hj θ β γ g)) =
        cutRestrHom (R := plusFactorAlgCat Q Λ Λc j hj θ β γ) Q Lt β γ
            (plusTailIncl Q Λ Λc j hj θ β γ) g.hom ∘ₗ
          (plusInnerEquiv Q Λ Λc j hj θ β γ N).toLinearMap := LinearMap.ext fun _ => rfl
    exact (cutStandardMap_comp Q Lt β γ _ (plusInnerEquiv Q Λ Λc j hj θ β γ N').toLinearMap
      x).symm.trans ((congrArg (fun f => cutStandardMap Q Lt β γ f x) h).trans
        (cutStandardMap_comp Q Lt β γ (plusInnerEquiv Q Λ Λc j hj θ β γ N).toLinearMap _ x))
  smul N c x := plusMid_smul_aux Q hQ Λ Λc j hj θ β γ N c x

/-- The relabelling of the algebra of `λ⁺` as the algebra of its three blocks. -/
def plusRelabel : TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (θ + (β + γ)) →ₐ[k]
    TensorProductAlgebra k Q (plusBlockLabels Λ Λc j hj) (θ + (β + γ)) :=
  (castLabelsTensorProductAlgebra Q (plusBlock_card j hj) (plusLabels Λ Λc j hj)
    (θ + (β + γ))).symm.toAlgHom

/-- The partial standardization at the outer cut of the three blocks of `λ⁺`, as a functor to
modules over `T^{λ⁺}`. -/
abbrev plusOuterCutFunctor :=
  cutStandardFunctor Q hQ (plusBlockLabels Λ Λc j hj) θ (β + γ) (plusRelabel Q Λ Λc j hj θ β γ)

/-- The identity of the inner standardization, onto its underlying module. -/
def plusMidEquiv (N : ModuleCat.{u} (plusFactorAlgCat Q Λ Λc j hj θ β γ)) :
    BlocksMid Q (plusBlockLabels Λ Λc j hj) θ β γ
        (PlusInput Q Λ Λc j hj θ β γ (PlusWrap Q Λ Λc j hj θ β γ N)) hQ ≃ₗ[cutFactorAlgebra Q
          (plusBlockLabels Λ Λc j hj) θ (β + γ)]
      (plusMidFunctor Q hQ Λ Λc j hj θ β γ).obj N where
  toFun n := n
  invFun n := n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem plusStandardFunctorIso_smul (N : ModuleCat.{u} (plusFactorAlgCat Q Λ Λc j hj θ β γ))
    (t : TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (θ + (β + γ)))
    (z : PlusStandard Q Λ Λc j hj θ β γ (PlusWrap Q Λ Λc j hj θ β γ N) hQ) :
    cutStandardMap Q (plusBlockLabels Λ Λc j hj) θ (β + γ)
        (plusMidEquiv Q hQ Λ Λc j hj θ β γ N).toLinearMap
        (plusStandardAction Q Λ Λc j hj θ β γ (PlusWrap Q Λ Λc j hj θ β γ N) hQ t z) =
      cutStandardAction Q (plusBlockLabels Λ Λc j hj) θ (β + γ)
        ((plusMidFunctor Q hQ Λ Λc j hj θ β γ).obj N) hQ (plusRelabel Q Λ Λc j hj θ β γ t)
        (cutStandardMap Q (plusBlockLabels Λ Λc j hj) θ (β + γ)
          (plusMidEquiv Q hQ Λ Λc j hj θ β γ N).toLinearMap z) :=
  cutStandardMap_action Q (plusBlockLabels Λ Λc j hj) θ (β + γ) hQ
    (plusMidEquiv Q hQ Λ Λc j hj θ β γ N).toLinearMap (plusRelabel Q Λ Λc j hj θ β γ t) z

/-- The component of `plusStandardFunctorIso`. -/
def plusStandardFunctorIsoEquiv (N : ModuleCat.{u} (plusFactorAlgCat Q Λ Λc j hj θ β γ)) :
    PlusStandardModule Q hQ Λ Λc j hj θ β γ N ≃ₗ[TensorProductAlgebra k Q (plusLabels Λ Λc j hj)
      (θ + (β + γ))] CutStandardModule Q (plusBlockLabels Λ Λc j hj) θ (β + γ) hQ
        (plusRelabel Q Λ Λc j hj θ β γ) ((plusMidFunctor Q hQ Λ Λc j hj θ β γ).obj N) where
  toFun := cutStandardMapEquiv Q (plusBlockLabels Λ Λc j hj) θ (β + γ)
    (plusMidEquiv Q hQ Λ Λc j hj θ β γ N)
  invFun := (cutStandardMapEquiv Q (plusBlockLabels Λ Λc j hj) θ (β + γ)
    (plusMidEquiv Q hQ Λ Λc j hj θ β γ N)).symm
  map_add' := map_add _
  map_smul' := plusStandardFunctorIso_smul Q hQ Λ Λc j hj θ β γ N
  left_inv := (cutStandardMapEquiv Q (plusBlockLabels Λ Λc j hj) θ (β + γ)
    (plusMidEquiv Q hQ Λ Λc j hj θ β γ N)).left_inv
  right_inv := (cutStandardMapEquiv Q (plusBlockLabels Λ Λc j hj) θ (β + γ)
    (plusMidEquiv Q hQ Λ Λc j hj θ β γ N)).right_inv

theorem plusStandardFunctorIso_naturality
    {N N' : ModuleCat.{u} (plusFactorAlgCat Q Λ Λc j hj θ β γ)} (g : N ⟶ N')
    (z : PlusStandard Q Λ Λc j hj θ β γ (PlusWrap Q Λ Λc j hj θ β γ N) hQ) :
    cutStandardMap Q (plusBlockLabels Λ Λc j hj) θ (β + γ)
        (plusMidEquiv Q hQ Λ Λc j hj θ β γ N').toLinearMap
        (plusStandardMap Q Λ Λc j hj θ β γ hQ (plusWrapHom Q Λ Λc j hj θ β γ g) z) =
      cutStandardMap Q (plusBlockLabels Λ Λc j hj) θ (β + γ)
        ((plusMidFunctor Q hQ Λ Λc j hj θ β γ).map g).hom
        (cutStandardMap Q (plusBlockLabels Λ Λc j hj) θ (β + γ)
          (plusMidEquiv Q hQ Λ Λc j hj θ β γ N).toLinearMap z) := by
  have h : (plusMidEquiv Q hQ Λ Λc j hj θ β γ N').toLinearMap ∘ₗ
      blocksMidHom Q (plusBlockLabels Λ Λc j hj) θ β γ hQ
        (plusInputHom Q Λ Λc j hj θ β γ (plusWrapHom Q Λ Λc j hj θ β γ g)) =
      ((plusMidFunctor Q hQ Λ Λc j hj θ β γ).map g).hom ∘ₗ
        (plusMidEquiv Q hQ Λ Λc j hj θ β γ N).toLinearMap := LinearMap.ext fun _ => rfl
  exact (cutStandardMap_comp Q (plusBlockLabels Λ Λc j hj) θ (β + γ) _
    (plusMidEquiv Q hQ Λ Λc j hj θ β γ N').toLinearMap z).symm.trans
      ((congrArg (fun f => cutStandardMap Q (plusBlockLabels Λ Λc j hj) θ (β + γ) f z) h).trans
        (cutStandardMap_comp Q (plusBlockLabels Λ Λc j hj) θ (β + γ)
          (plusMidEquiv Q hQ Λ Λc j hj θ β γ N).toLinearMap _ z))

/-- **The partial standardization of `λ⁺` with three blocks in two steps**: the standardization
at the inner cut followed by the standardization at the outer cut. -/
def plusStandardFunctorIso :
    plusStandardFunctor Q hQ Λ Λc j hj θ β γ ≅
      plusMidFunctor Q hQ Λ Λc j hj θ β γ ⋙ plusOuterCutFunctor Q hQ Λ Λc j hj θ β γ :=
  NatIso.ofComponents (fun N => (plusStandardFunctorIsoEquiv Q hQ Λ Λc j hj θ β γ N).toModuleIso)
    fun g => ModuleCat.hom_ext (LinearMap.ext fun z =>
      plusStandardFunctorIso_naturality Q hQ Λ Λc j hj θ β γ g z)

/-- **The partial standardization of `λ⁺` with three blocks is tensoring with a bimodule.** -/
theorem isTensorRepresented_plusStandardFunctor :
    IsTensorRepresented (plusStandardFunctor Q hQ Λ Λc j hj θ β γ) :=
  IsTensorRepresented.of_iso (plusStandardFunctorIso Q hQ Λ Λc j hj θ β γ).symm
    (isTensorRepresented_comp (plusMidFunctor_additive Q hQ Λ Λc j hj θ β γ)
      (cutStandardFunctor_additive Q hQ (plusBlockLabels Λ Λc j hj) θ (β + γ)
        (plusRelabel Q Λ Λc j hj θ β γ))
      (plusMidPresented Q hQ Λ Λc j hj θ β γ).isTensorRepresented
      (isTensorRepresented_cutStandardFunctor Q hQ (plusBlockLabels Λ Λc j hj) θ (β + γ)
        (plusRelabel Q Λ Λc j hj θ β γ)))

/-! ### `S_+` -/

variable (θh : Fin j → Multiset I) (θt : Fin (ℓ - j) → Multiset I)

/-- The standardizations of the first and of the last block of `S_+` are tensoring with a
bimodule. -/
theorem isTensorRepresented_plusOuterStd :
    IsTensorRepresented (plusOuterStd Q hQ Λ Λc j hj β θh θt) :=
  isTensorRepresented_comp (singStd_additive Q hQ _ _ _ _) _
    (isTensorRepresented_singStd Q hQ _ _ _ _)
    (isTensorRepresented_comp _ (additive_comp' (singStd_additive Q hQ _ _ _ _)
        inferInstance)
      (isTensorRepresented_restrictScalars _)
      (isTensorRepresented_comp (singStd_additive Q hQ _ _ _ _) _
        (isTensorRepresented_singStd Q hQ _ _ _ _) (isTensorRepresented_restrictScalars _)))

/-- **`S_+` is tensoring with a bimodule**: the partial standardization
`𝕊^{λ_1; …; λ_j; μ μ*; λ_{j+1}; …; λ_ℓ}` is represented by tensoring with its value on the
regular module (Webster, arXiv:1309.3796v3, §5.1). -/
theorem isTensorRepresented_plusStagedStd :
    IsTensorRepresented (plusStagedStd Q hQ Λ Λc j hj β θh θt) :=
  isTensorRepresented_comp inferInstance
    (plusStandardFunctor_additive Q hQ Λ Λc j hj (singWeight j θh) β (singWeight (ℓ - j) θt))
    (isTensorRepresented_plusOuterStd Q hQ Λ Λc j hj β θh θt)
    (isTensorRepresented_plusStandardFunctor Q hQ Λ Λc j hj _ β _)

end CupCap

end Categorification.Stendhal
