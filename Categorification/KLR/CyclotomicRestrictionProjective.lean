/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicFlip
import Categorification.KLR.CyclotomicProjective
import Categorification.WeightedKLR.Induction.Restriction

/-!
# Projectivity of cyclotomic restriction

Kang–Kashiwara, arXiv:1102.4677v4, Theorem 4.5 and Corollary 4.6:
the right-projectivity theorem for the induction corner, followed by horizontal
reflection, gives a projective left module for the restriction corner.
-/

noncomputable section

namespace Categorification.KLR.CycKLR
open KLRAlgebra KLRAlgebra.AbsentColour MulOpposite

variable {k I : Type*} [CommRing k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
  (a : I → Polynomial k) (β : Multiset I) (i : I)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Rl" => CycKLR k Q a β
local notation "Su" => CycKLR k Q a (Si + β)
local notation "Mc" => IndCorner Q i a β

/-- Identification of the module quotient in the proof of Theorem 4.5 with the
cyclotomic algebra quotient. -/
private def quotientEquiv (ν : Multiset I) : FLam Q ν a ≃ₗ[k] CycKLR k Q a ν :=
  (Submodule.Quotient.restrictScalarsEquiv k (cycIdeal Q a ν).asIdeal).symm.trans
    ((Submodule.quotEquivOfEq _ _ (show (cycIdeal Q a ν).asIdeal.restrictScalars k =
      LinearMap.ker (mk k Q a ν).toLinearMap by
        ext r
        exact (mk_eq_zero_iff r).symm)).trans
      ((mk k Q a ν).toLinearMap.quotKerEquivOfSurjective mk_surjective))

private theorem quotientEquiv_mk (ν : Multiset I) (r : KLRAlgebra k Q ν) :
    quotientEquiv a ν (Submodule.Quotient.mk r) = mk k Q a ν r := rfl

private theorem quotientEquiv_actF (r : KLRAlgebra k Q β) (z : FLam Q (Si + β) a) :
    quotientEquiv a (Si + β) (actF Q i β a r z) =
      quotientEquiv a (Si + β) z * cyclotomicLast Q i a β (mk k Q a β r) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [actF_mk, quotientEquiv_mk, map_mul, quotientEquiv_mk, cyclotomicLast_mk]

private def cornerLinear : FE Q i β a →ₗ[Rlᵐᵒᵖ] Mc where
  toFun z := ⟨quotientEquiv a (Si + β) z.1, by
    change _ * cyclotomicLast Q i a β 1 = _
    rw [← map_one (mk k Q a β), ← quotientEquiv_actF, actF_one_of_mem i β a z.2]⟩
  map_add' z w := Subtype.ext (map_add _ _ _)
  map_smul' r z := by
    obtain ⟨r, rfl⟩ := op_surjective r
    obtain ⟨r, rfl⟩ := mk_surjective r
    rw [op_mk_smul_FE]
    exact Subtype.ext (quotientEquiv_actF a β i r z.1)

/-- The right module from the proof of Kang–Kashiwara Theorem 4.5 is the
ordinary one-sided induction corner, including its right algebra action. -/
private def feEquivCorner : FE Q i β a ≃ₗ[Rlᵐᵒᵖ] Mc := by
  apply LinearEquiv.ofBijective (cornerLinear a β i)
  refine ⟨fun x y h => Subtype.ext ((quotientEquiv a (Si + β)).injective
    (congrArg (fun z : Mc => z.1) h)), ?_⟩
  intro z
  let w := (quotientEquiv a (Si + β)).symm z.1
  refine ⟨⟨actF Q i β a 1 w, actF_mem i β a 1 w⟩, Subtype.ext ?_⟩
  change quotientEquiv a (Si + β) (actF Q i β a 1 w) = z.1
  rw [quotientEquiv_actF, map_one, show quotientEquiv a (Si + β) w = z.1 from
    (quotientEquiv a (Si + β)).apply_symm_apply _]
  exact z.2

/-- **Kang–Kashiwara, arXiv:1102.4677v4, Theorem 4.5**, in corner form: the one-sided
corner `R^Λ({i} + β) e(β, i)` is a projective right `R^Λ(β)`-module, for `β ≠ 0`. -/
theorem projective_indCorner
    (hsym : KLRSymm Q)
    (hQ : ∀ s t : I, s ≠ t → ∃ c : k, IsUnit c ∧ (polyInY (Q s t)).leadingCoeff = Polynomial.C c)
    (ha : (a i).Monic) (hβ : 0 < β.card) : Module.Projective Rlᵐᵒᵖ Mc :=
  let := projective_FE i β a hsym (leadUnitAt_of i hQ) ha hβ
  Module.Projective.of_equiv (feEquivCorner a β i)

private theorem projective_res_regular_of_pos
    (hsym : KLRSymm Q)
    (hQ : ∀ s t : I, s ≠ t → ∃ c : k, IsUnit c ∧ (polyInY (Q s t)).leadingCoeff = Polynomial.C c)
    (ha : (a i).Monic) (hβ : 0 < β.card) : Module.Projective Rl (Res Q i a β Su) := by
  let : Module.Projective Rlᵐᵒᵖ Mc := projective_indCorner a β i hsym hQ ha hβ
  let φ : Rl →ₙ+* Su := cyclotomicLast Q i a β
  have : Module.Projective Rlᵐᵒᵖ (InductionAlong.Corner φ) :=
    Module.Projective.of_equiv' (show Mc ≃ₗ[Rlᵐᵒᵖ] InductionAlong.Corner φ from
      { toFun := fun z => ⟨z.1, z.2⟩
        invFun := fun z => ⟨z.1, z.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl })
  let ρ : Su →+ Su := ((opAddEquiv : Su ≃+ Suᵐᵒᵖ).symm.toAddMonoidHom).comp
    (flipEquiv a (Si + β)).toAlgHom.toAddMonoidHom
  exact InductionAlong.Res.projective_of_corner (φ := φ) ρ (flip_mul a _) (flip_flip a _)
    (flipEquiv a β).toRingEquiv (flip_cyclotomicLast a β i)

section Field

variable {F : Type*} [Field F] {Q : I → I → MvPolynomial (Fin 2) F}
  (a : I → Polynomial F)

local notation "R" => CycKLR F Q a β
local notation "S" => CycKLR F Q a (Si + β)

private theorem projective_res_vacuum (M : Type*) [AddCommGroup M] [Module F M]
    [Module (CycKLR F Q a (Si + 0)) M] [IsScalarTower F (CycKLR F Q a (Si + 0)) M] :
    Module.Projective (CycKLR F Q a 0) (Res Q i a 0 M) := by
  let σ := (cyclotomicZeroEquiv Q a).toRingEquiv
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  let e : Res Q i a 0 M ≃ₛₗ[(σ : CycKLR F Q a 0 →+* F)] Res Q i a 0 M :=
    { Equiv.refl _ with
      map_add' := fun _ _ => rfl
      map_smul' := fun r z => Subtype.ext (by
        change cyclotomicLast Q i a 0 r • z.1 = (cyclotomicZeroEquiv Q a r) • z.1
        rw [cyclotomicLast_zero_eq, smul_assoc, one_smul]) }
  exact Module.Projective.of_equiv e.symm

variable (hsym : KLRSymm Q)
  (hQ : ∀ s t : I, s ≠ t → ∃ c : F, IsUnit c ∧ (polyInY (Q s t)).leadingCoeff = Polynomial.C c)

include hsym hQ in
/-- Restriction preserves projectivity for finite projective modules, including
the edge at the highest weight (Kang–Kashiwara, arXiv:1102.4677v4, Corollary 4.6). -/
theorem projective_res (ha : (a i).Monic) (M : Type*) [AddCommGroup M] [Module F M]
    [Module S M] [IsScalarTower F S M] [Module.Finite S M] [Module.Projective S M] :
    Module.Projective R (Res Q i a β M) := by
  rcases eq_or_ne β 0 with rfl | h
  · exact projective_res_vacuum i a M
  · let φ : R →ₙ+* S := cyclotomicLast Q i a β
    have : Module.Projective R (InductionAlong.Res φ S) :=
      projective_res_regular_of_pos a β i hsym hQ ha (Multiset.card_pos.mpr h)
    exact InductionAlong.Res.projective_of_regular φ M

include hQ in
/-- Finite generation of cyclotomic restriction over a field, by the
finite-dimensionality in Kang–Kashiwara, arXiv:1102.4677v4, Corollary 4.4. -/
theorem finite_res (ha : ∀ j, (a j).Monic) (M : Type*) [AddCommGroup M] [Module F M]
    [Module S M] [IsScalarTower F S M] [Module.Finite S M] : Module.Finite R (Res Q i a β M) := by
  have : Module.Finite F S := module_finite (ν := Si + β) (fun s t h => by
    obtain ⟨c, hc, he⟩ := hQ s t h
    rw [he]
    exact hc.map Polynomial.C) ha
  have : Module.Finite F M := Module.Finite.trans S M
  exact Module.Finite.of_restrictScalars_finite F R _

end Field

end Categorification.KLR.CycKLR
