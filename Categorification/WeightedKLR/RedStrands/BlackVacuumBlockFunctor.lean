/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqVacuumImage

set_option backward.isDefEq.respectTransparency false

/-!
# The vacuum functor `Ř^λ-pmod ⟶ D(T^λ)` at one block

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 7.22 (b). The strongly equivariant functor `Φ = blackVacuumFunctor C₀` out of
`Ř^λ-pmod` (Corollary 3.27) is evaluated at one weight space and one block `β` of it
(`blackVacuumBlockFunctor`). On the images `u P_∅` of the vacuum and the 2-morphisms between
them it is computed by the derived action `blackPresCL` on `C₀`:

* `blackVacuumBlockWordIso`: `Φ(u P_∅)_β ≅ (u C₀)_β`, for every 1-morphism `u` out of the
  vacuum region (the equivariance isomorphism of `Φ` and `Φ(P_∅) ≅ C₀`);
* `blackVacuumBlockFunctor_map_vacEvG`: `Φ` sends the evaluation at `P_∅` of a 2-morphism
  `η : u ⟶ v` to the action of `η` on `C₀`, conjugated by these isomorphisms (Webster's
  condition of Definition 3.23).

For a strongly equivariant endofunctor `σ` of the derived action fixing `C₀` and acting on the
block `β` by `S'` (`hσ`), `blackVacuumBlockCompIso` is `Φ_β ⋙ S' ≅ Φ_β`, from
`blackVacuumImageIsoSelf`. This is the input `εΦ` of `SingleRed.derivedTensorIsoIdOfVacuum`.

The hypotheses are those of `blackVacuumFunctor`, including the route hypothesis `hΛ₀` of
`blackRouqFamily`.
-/

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits KLR TwoRep QuantumGroup KL3.Diagram CyclotomicAction
  DoubleDiagram StringDiagrams
open scoped Classical ZeroObject
open Pseudofunctor.StrongTrans

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u w u₁

noncomputable section

variable {I : Type u} {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {hQ : IsRouquierQ C Q}
  {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)
  [∀ β : Multiset I,
    _root_.HasDerivedCategory.{u} (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)]
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] {RD : UDot.WeightDatum C X Y} {Λ₀ : X}
  (hΛ₀ : ∀ i, RD.pair (RD.iY i) Λ₀ = ∑ r : Fin ℓ, (Λ r i : ℤ))
  (hsym : KLRSymm Q)

set_option hygiene false in
local notation "D" β => _root_.DerivedCategory (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)

variable (C₀ : ∀ β : WeightBlocks RD Λ₀ (blockWeight RD Λ₀ 0), D β.1)
  (hC₀ : ∀ β, β.1 ≠ 0 → IsZero (C₀ β))
  (c : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat) (β : WeightBlocks RD Λ₀ c.as.region)

/-- The block `β` of the weight space of the derived action at `c`. -/
def blackBlockEval : ((blackPresCL hP hwf hΛ₀ hsym).obj c).carrier ⥤ D β.1 :=
  Pi.eval (fun γ : WeightBlocks RD Λ₀ c.as.region => D γ.1) β

instance blackBlockEval_additive : (blackBlockEval hP hwf hΛ₀ hsym c β).Additive :=
  inferInstanceAs (Pi.eval (fun γ : WeightBlocks RD Λ₀ c.as.region => D γ.1) β).Additive

instance blackBlockEval_linear : (blackBlockEval hP hwf hΛ₀ hsym c β).Linear k where
  map_smul _ _ := rfl

/-- **The vacuum functor at the block `β`**: `Φ = blackVacuumFunctor C₀` at the region `c`,
followed by evaluation at the block `β`. -/
def blackVacuumBlockFunctor :
    ((univCyclotomicPresCLPmod.{u, u, u} hQ RD Λ₀ (blackLam_pair hΛ₀)).obj c).carrier ⥤ D β.1 :=
  ((blackVacuumFunctor hP hwf hΛ₀ hsym C₀ hC₀).app c).obj ⋙ blackBlockEval hP hwf hΛ₀ hsym c β

instance blackVacuumBlockFunctor_additive :
    (blackVacuumBlockFunctor hP hwf hΛ₀ hsym C₀ hC₀ c β).Additive := by
  unfold blackVacuumBlockFunctor; infer_instance

instance blackVacuumBlockFunctor_linear :
    (blackVacuumBlockFunctor hP hwf hΛ₀ hsym C₀ hC₀ c β).Linear k := by
  unfold blackVacuumBlockFunctor; infer_instance

/-- **The vacuum functor on an image of `P_∅`**: `Φ(u P_∅)_β ≅ (u C₀)_β` for a 1-morphism `u`
out of the vacuum region, from the equivariance isomorphism of `Φ` and `Φ(P_∅) ≅ C₀`. -/
def blackVacuumBlockWordIso (f : vacRegion hQ RD Λ₀ ⟶ c) :
    (blackVacuumBlockFunctor hP hwf hΛ₀ hsym C₀ hC₀ c β).obj
        (vacImg hQ RD Λ₀ (blackLam_pair hΛ₀) f) ≅
      (blackBlockEval hP hwf hΛ₀ hsym c β).obj
        (((blackPresCL hP hwf hΛ₀ hsym).map f).obj.obj C₀) :=
  (blackBlockEval hP hwf hΛ₀ hsym c β).mapIso
    ((StronglyEquivariant.iso (blackVacuumFunctor hP hwf hΛ₀ hsym C₀ hC₀) f).app
        (univVacuum hQ RD Λ₀ (blackLam_pair hΛ₀)) ≪≫
      ((blackPresCL hP hwf hΛ₀ hsym).map f).obj.mapIso
        (blackVacuumFunctorAppIso hP hwf hΛ₀ hsym C₀ hC₀))

/-- **The vacuum functor on 2-morphisms** (Webster's condition of Definition 3.23): `Φ` sends
the evaluation at `P_∅` of `η : u ⟶ v` to the action of `η` on `C₀`, conjugated by
`blackVacuumBlockWordIso`. -/
theorem blackVacuumBlockFunctor_map_vacEvG {f g : vacRegion hQ RD Λ₀ ⟶ c} (η : f ⟶ g) :
    (blackVacuumBlockFunctor hP hwf hΛ₀ hsym C₀ hC₀ c β).map
        (vacEvG hQ RD Λ₀ (blackLam_pair hΛ₀) η) =
      (blackVacuumBlockWordIso hP hwf hΛ₀ hsym C₀ hC₀ c β f).hom ≫
        (blackBlockEval hP hwf hΛ₀ hsym c β).map
          (((blackPresCL hP hwf hΛ₀ hsym).map₂ η).hom.app C₀) ≫
        (blackVacuumBlockWordIso hP hwf hΛ₀ hsym C₀ hC₀ c β g).inv := by
  have hW := StronglyEquivariant.webster_condition
    (blackVacuumFunctor hP hwf hΛ₀ hsym C₀ hC₀) η (univVacuum hQ RD Λ₀ (blackLam_pair hΛ₀))
  have hN := ((blackPresCL hP hwf hΛ₀ hsym).map₂ η).hom.naturality
    (blackVacuumFunctorAppIso hP hwf hΛ₀ hsym C₀ hC₀).hom
  rw [← cancel_mono (blackVacuumBlockWordIso hP hwf hΛ₀ hsym C₀ hC₀ c β g).hom, Category.assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp only [blackVacuumBlockWordIso, blackVacuumBlockFunctor, Functor.comp_map]
  rw [Functor.mapIso_hom, Functor.mapIso_hom]
  erw [← Functor.map_comp, ← Functor.map_comp]
  refine congrArg (blackBlockEval hP hwf hΛ₀ hsym c β).map ?_
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  symm
  rw [Category.assoc, hN, ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ _) hW.symm

omit [Field k] in
/-- The component at `c` of an isomorphism of strong transformations, as an isomorphism of
functors. -/
def strongTransIsoApp {B : Type*} [Bicategory B] {F G : Pseudofunctor B (LinearCat.{u, u, u + 1} k)}
    {η θ : F ⟶ G} (e : η ≅ θ) (a : B) : (η.app a).obj ≅ (θ.app a).obj where
  hom := (e.hom.as.app a).hom
  inv := (e.inv.as.app a).hom
  hom_inv_id := by
    have h := congrArg (fun m => (m.as.app a).hom) e.hom_inv_id
    exact h
  inv_hom_id := by
    have h := congrArg (fun m => (m.as.app a).hom) e.inv_hom_id
    exact h

/-- **`εΦ` at one block** (Webster, arXiv:1309.3796v3, proof of Proposition 7.22, "any choice of
isomorphism induces isomorphisms between functors"): a strongly equivariant endofunctor `σ` of
the derived action with `σ(C₀) ≅ C₀` (`e`), acting on the block `β` of the weight space at `c`
by `S'` (`hσ`), satisfies `Φ_β ⋙ S' ≅ Φ_β` for the vacuum functor `Φ`. -/
def blackVacuumBlockCompIso (σ : blackPresCL hP hwf hΛ₀ hsym ⟶ blackPresCL hP hwf hΛ₀ hsym)
    (e : (σ.app (vacRegion hQ RD Λ₀)).obj.obj C₀ ≅ C₀) (S' : (D β.1) ⥤ (D β.1))
    (hσ : (σ.app c).obj ⋙ blackBlockEval hP hwf hΛ₀ hsym c β ≅
      blackBlockEval hP hwf hΛ₀ hsym c β ⋙ S') :
    blackVacuumBlockFunctor hP hwf hΛ₀ hsym C₀ hC₀ c β ⋙ S' ≅
      blackVacuumBlockFunctor hP hwf hΛ₀ hsym C₀ hC₀ c β :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((blackVacuumFunctor hP hwf hΛ₀ hsym C₀ hC₀).app c).obj hσ.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (strongTransIsoApp (blackVacuumImageIsoSelf hP hwf hΛ₀ hsym C₀ hC₀ σ e) c)
      (blackBlockEval hP hwf hΛ₀ hsym c β)

end

end Categorification.Stendhal
