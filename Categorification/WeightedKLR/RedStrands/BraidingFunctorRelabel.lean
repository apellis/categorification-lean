/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorTwist
import Categorification.WeightedKLR.RedStrands.BraidingFunctor
import Categorification.WeightedKLR.RedStrands.RightStandardRelabel

set_option backward.isDefEq.respectTransparency false

/-!
# Relabelling the red strands of the braiding functors

Part of the proof of B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, Theorem 6.15. A ring isomorphism `f : A ≃+* B` with `f e = d`, `f e' = d'`
restricts to an isomorphism of bimodules `e A e' ≅ d B d'` over the isomorphisms of corners, so
it conjugates the derived tensor products by the twist equivalences
(`derivedRightTensorCornerBimoduleConjIso`), and one is an equivalence when the other is.

For a permutation `σ` of the red labels, relabelling the red strands (`violRedPermEquiv`) sends
`e_κ` to `e_{σ ∘ κ}`, so the braiding functor `𝔅^λ(σ ∘ κ', σ ∘ κ)` is conjugate to
`𝔅^{λ ∘ σ}(κ', κ)` (`braidingFunctorRelabelConjIso`) and is an equivalence when that one is
(`isEquivalence_braidingFunctor_relabel`). The braiding functor from a red order to itself is an
equivalence (`isEquivalence_braidingFunctor_self`).
-/

noncomputable section

namespace Categorification

open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

section Inverses

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]

/-- A functor `G` such that `F ⋙ G` and `G ⋙ X` are equivalences is an equivalence: it has a
right inverse and a left inverse, which are then isomorphic. -/
theorem isEquivalence_of_comp_left_of_comp_right (F : A ⥤ B) (G : B ⥤ C) (X : C ⥤ D)
    (hF : (F ⋙ G).IsEquivalence) (hX : (G ⋙ X).IsEquivalence) : G.IsEquivalence := by
  let R : C ⥤ B := (F ⋙ G).inv ⋙ F
  let L : C ⥤ B := X ⋙ (G ⋙ X).inv
  let hL : G ⋙ L ≅ 𝟭 B :=
    (Functor.associator G X (G ⋙ X).inv).symm ≪≫ (G ⋙ X).asEquivalence.unitIso.symm
  let hR : R ⋙ G ≅ 𝟭 C :=
    Functor.associator (F ⋙ G).inv F G ≪≫ (F ⋙ G).asEquivalence.counitIso
  let hRL : R ≅ L := (Functor.rightUnitor R).symm ≪≫ Functor.isoWhiskerLeft R hL.symm ≪≫
    (Functor.associator R G L).symm ≪≫ Functor.isoWhiskerRight hR L ≪≫ Functor.leftUnitor L
  exact (CategoryTheory.Equivalence.mk G R (hL.symm ≪≫ Functor.isoWhiskerLeft G hRL.symm)
    hR).isEquivalence_functor

end Inverses

section CornerBimodule

variable {A B : Type} [Ring A] [Ring B] (f : A ≃+* B) {e e' : A} {d d' : B}
  {he : IsIdempotentElem e} {he' : IsIdempotentElem e'} {hd : IsIdempotentElem d}
  {hd' : IsIdempotentElem d'} (hf : f e = d) (hf' : f e' = d')

/-- A ring isomorphism with `f e = d`, `f e' = d'` restricts to `e A e' ≃ d B d'`. -/
def cornerBimoduleRingEquiv : cornerBimodule e e' ≃+ cornerBimodule d d' where
  toFun x := ⟨f x.1, by rw [← hf, ← map_mul, x.2.1], by rw [← hf', ← map_mul, x.2.2]⟩
  invFun y := ⟨f.symm y.1, by rw [← f.symm_apply_apply e, hf, ← map_mul, y.2.1],
    by rw [← f.symm_apply_apply e', hf', ← map_mul, y.2.2]⟩
  left_inv x := Subtype.ext (f.symm_apply_apply _)
  right_inv y := Subtype.ext (f.apply_symm_apply _)
  map_add' x y := Subtype.ext (map_add f _ _)

variable [DG.HasDerivedCategory.{0, 0} he.Cornerᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} he'.Cornerᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} hd.Cornerᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} hd'.Cornerᵐᵒᵖ]

/-- **A ring isomorphism conjugates the derived tensor products with corner bimodules**:
`(- ⊗ᴸ e A e') ⋙ T ≅ T ⋙ (- ⊗ᴸ d B d')`, for the twist equivalences `T` along the
isomorphisms of corners. -/
def derivedRightTensorCornerBimoduleConjIso :
    derivedRightTensor.{0} he.Corner he'.Corner (cornerBimodule e e') ⋙
        derivedRightTensor.{0} he'.Corner hd'.Corner
          (TwistBimodule (he'.cornerRingEquiv hd' f hf')) ≅
      derivedRightTensor.{0} he.Corner hd.Corner (TwistBimodule (he.cornerRingEquiv hd f hf)) ⋙
        derivedRightTensor.{0} hd.Corner hd'.Corner (cornerBimodule d d') :=
  derivedRightTensorTwistConjIso (he.cornerRingEquiv hd f hf) (he'.cornerRingEquiv hd' f hf')
    (cornerBimoduleRingEquiv f hf hf') (fun c x => Subtype.ext (map_mul f c.1 x.1))
    (fun c x => Subtype.ext (map_mul f x.1 c.unop.1))

include f hf hf' in
/-- If `- ⊗ᴸ d B d'` is an equivalence, so is `- ⊗ᴸ e A e'`. -/
theorem isEquivalence_derivedRightTensor_cornerBimodule_of_ringEquiv
    (h : (derivedRightTensor.{0} hd.Corner hd'.Corner (cornerBimodule d d')).IsEquivalence) :
    (derivedRightTensor.{0} he.Corner he'.Corner (cornerBimodule e e')).IsEquivalence :=
  isEquivalence_derivedRightTensor_of_twistConj (he.cornerRingEquiv hd f hf)
    (he'.cornerRingEquiv hd' f hf') (cornerBimoduleRingEquiv f hf hf')
    (fun c x => Subtype.ext (map_mul f c.1 x.1)) (fun c x => Subtype.ext (map_mul f x.1 c.unop.1))

end CornerBimodule

section Self

variable {A : Type} [Ring A] {e : A} (he : IsIdempotentElem e)

/-- The bimodule `e A e` is the corner `e A e` itself. -/
def cornerBimoduleSelfTwistEquiv :
    cornerBimodule e e ≃ₗ[he.Cornerᵐᵒᵖ] TwistBimodule (RingEquiv.refl he.Corner) where
  toFun x := LeftTwist.of _ _ ⟨x.1, (Subsemigroup.mem_corner_iff he).2 ⟨x.2.1, x.2.2⟩⟩
  invFun y := ⟨((LeftTwist.of _ _).symm y).1, CornerEndomorphism.corner_mul_left he _,
    CornerEndomorphism.corner_mul_right he _⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [DG.HasDerivedCategory.{0, 0} he.Cornerᵐᵒᵖ]

/-- `- ⊗ᴸ e A e` is an equivalence. -/
theorem isEquivalence_derivedRightTensor_cornerBimodule_self :
    (derivedRightTensor.{0} he.Corner he.Corner (cornerBimodule e e)).IsEquivalence :=
  have : (derivedRightTensor.{0} he.Corner he.Corner
      (TwistBimodule (RingEquiv.refl he.Corner))).IsEquivalence :=
    (twistEquivalence (RingEquiv.refl he.Corner)).isEquivalence_functor
  Functor.isEquivalence_of_iso
    (derivedRightTensorIsoOfEquiv (cornerBimoduleSelfTwistEquiv he) (fun _ _ => rfl)).symm

end Self

end Categorification

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory KLR Equiv
open scoped DG.DegreeZero

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  (σ : Perm (Fin ℓ))
  [∀ (Ω : Fin ℓ → I →₀ ℕ) (κ₀ : List (Fin ℓ)),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k) (Q := Q) (Λ := Ω) (ν := ν) κ₀)ᵐᵒᵖ]

omit [∀ (Ω : Fin ℓ → I →₀ ℕ) (κ₀ : List (Fin ℓ)),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k) (Q := Q) (Λ := Ω) (ν := ν) κ₀)ᵐᵒᵖ] in
theorem violRedPermEquiv_symm_redProj (κ : List (Fin ℓ)) :
    (violRedPermEquiv (k := k) (Q := Q) (Λ' := Λ ∘ σ) (Λ := Λ) (ν := ν) σ
      (fun _ => rfl)).toRingEquiv.symm (violMk k Q Λ ν (redProj k Q Λ ν (κ.map σ))) =
      violMk k Q (Λ ∘ σ) ν (redProj k Q (Λ ∘ σ) ν κ) :=
  (RingEquiv.symm_apply_eq _).2 (violRedPermEquiv_redProj σ κ).symm

/-- **Relabelling conjugates the braiding functors**: `𝔅^λ(σ ∘ κ', σ ∘ κ)` is conjugate to
`𝔅^{λ ∘ σ}(κ', κ)` by the twist equivalences along the relabelling of corners. -/
def braidingFunctorRelabelConjIso (κ' κ : List (Fin ℓ)) :
    braidingFunctor.{0} k Q Λ ν (κ'.map σ) (κ.map σ) ⋙
        derivedRightTensor.{0} _ _ (TwistBimodule
          ((isIdempotentElem_violMk_redProj k Q Λ ν (κ.map σ)).cornerRingEquiv
            (isIdempotentElem_violMk_redProj k Q (Λ ∘ σ) ν κ)
            (violRedPermEquiv σ (fun _ => rfl)).toRingEquiv.symm
            (violRedPermEquiv_symm_redProj σ κ))) ≅
      derivedRightTensor.{0} _ _ (TwistBimodule
          ((isIdempotentElem_violMk_redProj k Q Λ ν (κ'.map σ)).cornerRingEquiv
            (isIdempotentElem_violMk_redProj k Q (Λ ∘ σ) ν κ')
            (violRedPermEquiv σ (fun _ => rfl)).toRingEquiv.symm
            (violRedPermEquiv_symm_redProj σ κ'))) ⋙
        braidingFunctor.{0} k Q (Λ ∘ σ) ν κ' κ :=
  derivedRightTensorCornerBimoduleConjIso _ _ _

/-- **Relabelling preserves equivalences of braiding functors**: if `𝔅^{λ ∘ σ}(κ', κ)` is an
equivalence, so is `𝔅^λ(σ ∘ κ', σ ∘ κ)`. -/
theorem isEquivalence_braidingFunctor_relabel {κ' κ κ₁ κ₂ : List (Fin ℓ)} (h₁ : κ'.map σ = κ₁)
    (h₂ : κ.map σ = κ₂) (h : (braidingFunctor.{0} k Q (Λ ∘ σ) ν κ' κ).IsEquivalence) :
    (braidingFunctor.{0} k Q Λ ν κ₁ κ₂).IsEquivalence := by
  subst h₁ h₂
  exact isEquivalence_derivedRightTensor_cornerBimodule_of_ringEquiv
    (violRedPermEquiv σ (fun _ => rfl)).toRingEquiv.symm (violRedPermEquiv_symm_redProj σ κ')
    (violRedPermEquiv_symm_redProj σ κ) h

/-- The braiding functor from a red order to itself is an equivalence. -/
theorem isEquivalence_braidingFunctor_self (κ : List (Fin ℓ)) :
    (braidingFunctor.{0} k Q Λ ν κ κ).IsEquivalence :=
  isEquivalence_derivedRightTensor_cornerBimodule_self _

/-- **A braiding functor that is the middle of two equivalences after relabelling**: if
`F ⋙ 𝔅^λ(σ ∘ κ', σ ∘ κ)` and `𝔅^{λ ∘ σ}(κ', κ) ⋙ G` are equivalences, then
`𝔅^λ(σ ∘ κ', σ ∘ κ)` is an equivalence. -/
theorem isEquivalence_braidingFunctor_of_relabel_comp {κ' κ κ₁ κ₂ : List (Fin ℓ)}
    (h₁ : κ'.map σ = κ₁) (h₂ : κ.map σ = κ₂) {D E : Type*} [Category D] [Category E]
    (F : D ⥤ DG.DerivedCategory.{0} (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ₁)ᵐᵒᵖ)
    (hF : (F ⋙ braidingFunctor.{0} k Q Λ ν κ₁ κ₂).IsEquivalence)
    (G : DG.DerivedCategory.{0}
      (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ σ) (ν := ν) κ)ᵐᵒᵖ ⥤ E)
    (hG : (braidingFunctor.{0} k Q (Λ ∘ σ) ν κ' κ ⋙ G).IsEquivalence) :
    (braidingFunctor.{0} k Q Λ ν κ₁ κ₂).IsEquivalence := by
  subst h₁ h₂
  set Tψ := derivedRightTensor.{0} (isIdempotentElem_violMk_redProj k Q Λ ν (κ.map σ)).Corner
    (isIdempotentElem_violMk_redProj k Q (Λ ∘ σ) ν κ).Corner (TwistBimodule
    ((isIdempotentElem_violMk_redProj k Q Λ ν (κ.map σ)).cornerRingEquiv
      (isIdempotentElem_violMk_redProj k Q (Λ ∘ σ) ν κ)
      (violRedPermEquiv σ (fun _ => rfl)).toRingEquiv.symm
      (violRedPermEquiv_symm_redProj σ κ)))
  set Tφ := derivedRightTensor.{0} (isIdempotentElem_violMk_redProj k Q Λ ν (κ'.map σ)).Corner
    (isIdempotentElem_violMk_redProj k Q (Λ ∘ σ) ν κ').Corner (TwistBimodule
    ((isIdempotentElem_violMk_redProj k Q Λ ν (κ'.map σ)).cornerRingEquiv
      (isIdempotentElem_violMk_redProj k Q (Λ ∘ σ) ν κ')
      (violRedPermEquiv σ (fun _ => rfl)).toRingEquiv.symm
      (violRedPermEquiv_symm_redProj σ κ')))
  have : Tφ.IsEquivalence := (twistEquivalence _).isEquivalence_functor
  have : (braidingFunctor.{0} k Q (Λ ∘ σ) ν κ' κ ⋙ G).IsEquivalence := hG
  have : (Tφ ⋙ braidingFunctor.{0} k Q (Λ ∘ σ) ν κ' κ ⋙ G).IsEquivalence := inferInstance
  let e : Tφ ⋙ braidingFunctor.{0} k Q (Λ ∘ σ) ν κ' κ ⋙ G ≅
      braidingFunctor.{0} k Q Λ ν (κ'.map σ) (κ.map σ) ⋙ Tψ ⋙ G :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (braidingFunctorRelabelConjIso σ κ' κ).symm G ≪≫
      Functor.associator _ _ _
  exact isEquivalence_of_comp_left_of_comp_right F _ (Tψ ⋙ G) hF
    (Functor.isEquivalence_of_iso e)

end Categorification.Stendhal.BraidedStendhalAlgebra
