import Categorification.TwoRep.ShiftedMatesWhisker

/-!
# Reassociation of shifted mates

The mate of the actual associator for composite adjunctions is the associator on the
reversed right adjoints. Thus homogeneous endomorphisms can be transported between the
two triple parenthesizations without assuming strict associativity or cyclicity.
`StrongSl2.mateCross_braid` then transports the braid relation to the actual local
crossings on a common left-associated triple, retaining the weight-shifted right adjoints.
This does not remove those shifts or assert an all-strand unshifted nilHecke action.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
universe w v u

private theorem conjugate_associator_inv {D : Type*} [Bicategory D]
    {a b c d : D} {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}
    {f₃ : c ⟶ d} {g₃ : d ⟶ c}
    (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) (adj₃ : f₃ ⊣ g₃) :
    conjugateEquiv ((adj₁.comp adj₂).comp adj₃)
      (adj₁.comp (adj₂.comp adj₃)) (α_ f₁ f₂ f₃).inv = (α_ g₃ g₂ g₁).inv := by
  apply (cancel_epi (α_ g₃ g₂ g₁).hom).mp
  rw [← Bicategory.conjugateEquiv_associator_hom adj₁ adj₂ adj₃,
    Bicategory.conjugateEquiv_comp, Iso.inv_hom_id, Bicategory.conjugateEquiv_id,
    Bicategory.conjugateEquiv_associator_hom, Iso.hom_inv_id]

private theorem conjugate_reassociate {D : Type*} [Bicategory D]
    {a b c d : D} {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}
    {f₃ : c ⟶ d} {g₃ : d ⟶ c}
    (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) (adj₃ : f₃ ⊣ g₃)
    (φ : (f₁ ≫ f₂) ≫ f₃ ⟶ (f₁ ≫ f₂) ≫ f₃) :
    conjugateEquiv (adj₁.comp (adj₂.comp adj₃)) (adj₁.comp (adj₂.comp adj₃))
      ((α_ f₁ f₂ f₃).inv ≫ φ ≫ (α_ f₁ f₂ f₃).hom) =
      (α_ g₃ g₂ g₁).hom ≫
        conjugateEquiv ((adj₁.comp adj₂).comp adj₃) ((adj₁.comp adj₂).comp adj₃) φ ≫
        (α_ g₃ g₂ g₁).inv := by
  rw [← Bicategory.conjugateEquiv_comp _ ((adj₁.comp adj₂).comp adj₃),
    ← Bicategory.conjugateEquiv_comp _ ((adj₁.comp adj₂).comp adj₃),
    Bicategory.conjugateEquiv_associator_hom, conjugate_associator_inv]
  simp only [Category.assoc]

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [GradedBicategory.ShiftCoherence B]
open GradedHomBicat
variable {a b c e : B} {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}
  {f₃ : c ⟶ e} {g₃ : e ⟶ c}

/-- Reassociation before taking mates becomes reverse reassociation afterwards,
with the same integer degree and the supplied composite adjunctions. -/
theorem mateSh_reassociate (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) (adj₃ : f₃ ⊣ g₃)
    {d : ℤ} (φ : ShiftedHom ((f₁ ≫ f₂) ≫ f₃) ((f₁ ≫ f₂) ≫ f₃) d) :
    mateSh (adj₁.comp (adj₂.comp adj₃))
      ((ShiftedHom.mk₀ (0 : ℤ) rfl (α_ f₁ f₂ f₃).inv).comp
        (φ.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (α_ f₁ f₂ f₃).hom) (zero_add d))
        (add_zero d)) =
      (ShiftedHom.mk₀ (0 : ℤ) rfl (α_ g₃ g₂ g₁).hom).comp
        ((mateSh ((adj₁.comp adj₂).comp adj₃) φ).comp
          (ShiftedHom.mk₀ (0 : ℤ) rfl (α_ g₃ g₂ g₁).inv) (zero_add d)) (add_zero d) := by
  apply of₂_injective d
  simp only [of₂_mateSh, ← of₂_comp_of₂, ← incl₂_eq_of₂,
    ← associator_inv_eq, ← associator_hom_eq, mapAdjunction_comp]
  exact conjugate_reassociate (mapAdjunction adj₁) (mapAdjunction adj₂) (mapAdjunction adj₃) _

namespace StrongSl2

open CategoryTheory.Limits
variable {k : Type*} [Field k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  (S : StrongSl2 k B)

/-- The crossing of the first two right-adjoint factors, on a left-associated triple. -/
def mateCrossTripleLeft (r : ℤ) :
    ShiftedHom ((S.adjointF (r + 1 + 1) ≫ S.adjointF (r + 1)) ≫ S.adjointF r)
      ((S.adjointF (r + 1 + 1) ≫ S.adjointF (r + 1)) ≫ S.adjointF r) (-2 : ℤ) :=
  shWhiskerRight (S.mateCross (r + 1)) (S.adjointF r)

/-- The other local crossing, conjugated by the actual associator to the same triple. -/
def mateCrossTripleRight (r : ℤ) :
    ShiftedHom ((S.adjointF (r + 1 + 1) ≫ S.adjointF (r + 1)) ≫ S.adjointF r)
      ((S.adjointF (r + 1 + 1) ≫ S.adjointF (r + 1)) ≫ S.adjointF r) (-2 : ℤ) :=
  (ShiftedHom.mk₀ (0 : ℤ) rfl
    (α_ (S.adjointF (r + 1 + 1)) (S.adjointF (r + 1)) (S.adjointF r)).hom).comp
    ((shWhiskerLeft (S.adjointF (r + 1 + 1)) (S.mateCross r)).comp
      (ShiftedHom.mk₀ (0 : ℤ) rfl
        (α_ (S.adjointF (r + 1 + 1)) (S.adjointF (r + 1)) (S.adjointF r)).inv)
      (by norm_num : (0 : ℤ) + -2 = -2)) (by norm_num : (-2 : ℤ) + 0 = -2)

/-- The actual local downward crossings satisfy the degree `-6` braid relation.
All weight-dependent shifts on the right adjoints are retained; no equality of distinct
triple parenthesizations or cyclicity hypothesis is imposed. -/
theorem mateCross_braid (r : ℤ) :
    ((S.mateCrossTripleLeft r).comp (S.mateCrossTripleRight r)
      (by norm_num : (-2 : ℤ) + -2 = -4)).comp (S.mateCrossTripleLeft r)
      (by norm_num : (-2 : ℤ) + -4 = -6) =
    ((S.mateCrossTripleRight r).comp (S.mateCrossTripleLeft r)
      (by norm_num : (-2 : ℤ) + -2 = -4)).comp (S.mateCrossTripleRight r)
      (by norm_num : (-2 : ℤ) + -4 = -6) := by
  have h := congrArg (mateSh ((S.adj r).comp
    ((S.adj (r + 1)).comp (S.adj (r + 1 + 1))))) (S.braid r)
  simp only [mateSh_comp, mateCross_tensor_first, mateSh_reassociate,
    mateSh_comp_shWhiskerRight] at h
  apply of₂_injective (-6)
  have h' := congrArg (of₂ (-6)) h
  simpa only [mateCrossTripleLeft, mateCrossTripleRight, mateCross,
    ← of₂_comp_of₂, Category.assoc] using h'

end StrongSl2
end Categorification.TwoRep
