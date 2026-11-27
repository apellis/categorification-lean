/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlong

/-!
# Induction along compatible ring maps and restriction of scalars

Let `πA : A → A'` and `πB : B → B'` be ring maps and `φ : A →ₙ+* B`, `φ' : A' →ₙ+* B'`
nonunital ring maps with `πB ∘ φ = φ' ∘ πA`. The map `z ⊗ n ↦ πB(z) ⊗ n` is a natural
transformation `baseChange : res_{πA} ⋙ Ind_φ ⟶ Ind_{φ'} ⋙ res_{πB}` from induction of a
restricted module to the restriction of the induced module. It is compatible with
composites of inductions (`baseChange_comp`) and with the element maps of intertwining
elements that correspond under `πB` (`baseChange_natTrans`).

This is the shape of the crossing of a downward black strand with a red line in the
cyclotomic representation of Webster's `𝒯` (arXiv:1309.3796v3, §4.6, proof of Theorem 4.25),
where `πA` and `πB` are the quotient maps between cyclotomic KLR algebras.
-/

namespace Categorification

open CategoryTheory MulOpposite

noncomputable section

namespace InductionAlong

universe u w

variable {A A' B B' C C' : Type u} [Ring A] [Ring A'] [Ring B] [Ring B'] [Ring C] [Ring C']
  (πA : A →+* A') (πB : B →+* B') (πC : C →+* C')
  {φ : A →ₙ+* B} {φ' : A' →ₙ+* B'} (hφ : ∀ x, πB (φ x) = φ' (πA x))

include hφ

/-- The image of a corner element. -/
def cornerBase (z : Corner φ) : Corner φ' :=
  ⟨πB z.1, by
    change πB z.1 * φ' 1 = πB z.1
    rw [← map_one πA, ← hφ, ← map_mul]
    exact congrArg πB z.2⟩

theorem cornerBase_val (z : Corner φ) : (cornerBase πA πB hφ z).1 = πB z.1 := rfl

/-- The component `z ⊗ n ↦ πB(z) ⊗ n` of `baseChange`. -/
def baseMap (N : ModuleCat.{max u w} A') :
    Ind ((ModuleCat.restrictScalars.{max u w} πA).obj N) φ →ₗ[B]
      (ModuleCat.restrictScalars.{max u w} πB).obj ((functor.{u, w} φ').obj N) :=
  Ind.lift (fun z n => (Ind.tmul (cornerBase πA πB hφ z) n : Ind N φ'))
    (fun z z' n => by
      rw [show cornerBase πA πB hφ (z + z') = cornerBase πA πB hφ z + cornerBase πA πB hφ z'
        from Subtype.ext (map_add πB _ _)]
      exact Ind.add_tmul _ _ _)
    (fun z n n' => Ind.tmul_add _ _ _)
    (fun z a n => by
      rw [show cornerBase πA πB hφ (op a • z) = op (πA a) • cornerBase πA πB hφ z from
        Subtype.ext (by
          change πB (z.1 * φ a) = πB z.1 * φ' (πA a)
          rw [map_mul, hφ])]
      exact Ind.op_smul_tmul _ _ _)
    (fun b z n => by
      rw [show cornerBase πA πB hφ (b • z) = πB b • cornerBase πA πB hφ z from
        Subtype.ext (map_mul πB _ _)]
      exact (Ind.smul_tmul _ _ _).symm)

@[simp] theorem baseMap_tmul (N : ModuleCat.{max u w} A') (z : Corner φ) (n : N) :
    baseMap πA πB hφ N (Ind.tmul z n) = (Ind.tmul (cornerBase πA πB hφ z) n : Ind N φ') :=
  rfl

/-- **Induction commutes with restriction of scalars along compatible maps**: the natural
transformation `z ⊗ n ↦ πB(z) ⊗ n`. -/
def baseChange :
    ModuleCat.restrictScalars.{max u w} πA ⋙ functor.{u, w} φ ⟶
      functor.{u, w} φ' ⋙ ModuleCat.restrictScalars.{max u w} πB where
  app N := ModuleCat.ofHom
    (X := ↑((ModuleCat.restrictScalars.{max u w} πA ⋙ functor.{u, w} φ).obj N))
    (Y := ↑((functor.{u, w} φ' ⋙ ModuleCat.restrictScalars.{max u w} πB).obj N))
    (baseMap πA πB hφ N)
  naturality _ _ _ := ModuleCat.hom_ext (Ind.ext fun _ _ => rfl)

theorem baseChange_app_tmul (N : ModuleCat.{max u w} A') (z : Corner φ) (n : N) :
    (baseChange.{u, w} πA πB hφ).app N (Ind.tmul z n) =
      (Ind.tmul (cornerBase πA πB hφ z) n : Ind N φ') :=
  rfl

variable {ψ : B →ₙ+* C} {ψ' : B' →ₙ+* C'} (hψ : ∀ x, πC (ψ x) = ψ' (πB x))

include hψ in

/-- **Base change is compatible with composites of inductions.** -/
theorem baseChange_comp :
    Functor.whiskerRight (baseChange.{u, w} πA πB hφ) (functor ψ) ≫
        Functor.whiskerLeft (functor φ') (baseChange.{u, w} πB πC hψ) ≫
        Functor.whiskerRight (compIso.{u, w} φ' ψ').hom (ModuleCat.restrictScalars πC) =
      Functor.whiskerLeft (ModuleCat.restrictScalars πA) (compIso.{u, w} φ ψ).hom ≫
        baseChange.{u, w} πA πC (φ := ψ.comp φ) (φ' := ψ'.comp φ')
          (fun x => by rw [NonUnitalRingHom.comp_apply, NonUnitalRingHom.comp_apply, hψ, hφ]) := by
  refine NatTrans.ext (funext fun N => ModuleCat.hom_ext (Ind.ext₂ fun z w n => ?_))
  refine congrArg (Ind.tmul · n) (Subtype.ext ?_)
  change πC z.1 * ψ' (πB w.1) = πC (z.1 * ψ w.1)
  rw [map_mul, hψ]

/-- **Base change is compatible with the element maps of corresponding intertwiners.** -/
theorem baseChange_natTrans {χ : A →ₙ+* B} {χ' : A' →ₙ+* B'}
    (hχ : ∀ x, πB (χ x) = χ' (πA x)) {x : B} {x' : B'} (hx : Intertwines φ χ x)
    (hx' : Intertwines φ' χ' x') (hπx : πB x = x') :
    Functor.whiskerLeft (ModuleCat.restrictScalars πA) (natTrans.{u, w} hx) ≫
        baseChange.{u, w} πA πB hχ =
      baseChange.{u, w} πA πB hφ ≫
        Functor.whiskerRight (natTrans.{u, w} hx') (ModuleCat.restrictScalars πB) := by
  refine NatTrans.ext (funext fun N => ModuleCat.hom_ext (Ind.ext fun z n => ?_))
  refine congrArg (Ind.tmul · n) (Subtype.ext ?_)
  change πB (z.1 * x) = πB z.1 * x'
  rw [map_mul, hπx]

end InductionAlong

end

end Categorification
