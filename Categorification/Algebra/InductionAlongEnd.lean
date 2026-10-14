/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlong
import Categorification.Algebra.ModuleCatLinear
import Categorification.KLR.BaseChange

/-!
# Endomorphisms of an induction given by elements, as a `k`-linear antihomomorphism

Let `Φ : A →ₙ+* D` be a nonunital ring map into an algebra `D` over a commutative ring `k`.
The elements `x : D` with `Φ a * x = x * Φ a` for all `a` form a `k`-subalgebra
`selfInt k Φ` of `D`. For a functor `G` with an identification `e : G ≅ Ind_Φ`,
`x ↦ e.hom ≫ natTrans x ≫ e.inv` is a `k`-linear, unital map `selfInt k Φ → End G`
reversing products (`endHom`), since `End G` is multiplied by composition in the opposite
order. Hence polynomial expressions `ncEval` in endomorphisms of `G` represented by elements
are represented by the same expressions in `D`, read with the variables reversed
(`endHom_ncEval`). This turns the polynomial right-hand sides of the KLR relations,
evaluated in `End` of a composite of induction functors as in `TwoRep.RouqUpKLR`, into
polynomials in the dots of `D`.
-/

namespace Categorification.InductionAlong

open CategoryTheory

universe u w v

noncomputable section

variable (k : Type v) [CommRing k] {A D : Type u} [Ring A] [Ring D] [Algebra k D]

/-- The `k`-subalgebra of elements commuting with the image of `Φ`. -/
def selfInt (Φ : A →ₙ+* D) : Subalgebra k D where
  carrier := {x | Intertwines Φ Φ x}
  mul_mem' hx hy := Intertwines.mul hx hy
  add_mem' hx hy := Intertwines.add hx hy
  algebraMap_mem' c a := (Algebra.commutes c (Φ a)).symm

variable {k}

theorem Intertwines.smul {Φ Ψ : A →ₙ+* D} {x : D} (hx : Intertwines Φ Ψ x) (c : k) :
    Intertwines Φ Ψ (c • x) := fun a => by rw [mul_smul_comm, hx a, smul_mul_assoc]

/-- Element transformations are `k`-linear in the element. -/
theorem natTrans_smul {Φ Ψ : A →ₙ+* D} {x : D} (hx : Intertwines Φ Ψ x) (c : k) :
    natTrans.{u, w} (hx.smul c) = c • natTrans hx := by
  ext N : 2
  refine ModuleCat.hom_ext (Ind.ext fun z n => ?_)
  change Ind.tmul (cornerMul (hx.smul c) z) n =
    algebraMap k D c • (Ind.tmul (cornerMul hx z) n : Ind N Ψ)
  rw [Ind.smul_tmul]
  congr 1
  apply Subtype.ext
  change z.1 * (c • x) = algebraMap k D c * (z.1 * x)
  rw [Algebra.smul_def, ← mul_assoc, ← Algebra.commutes, mul_assoc]

variable {G : ModuleCat.{max u w} A ⥤ ModuleCat.{max u w} D} {Φ : A →ₙ+* D}

theorem selfInt.intertwines (x : selfInt k Φ) : Intertwines Φ Φ x.1 := x.2

/-- The endomorphism of `G` given by a self-intertwining element. -/
def endHom (e : G ≅ functor.{u, w} Φ) : selfInt k Φ →ₗ[k] End G where
  toFun x := e.hom ≫ natTrans (selfInt.intertwines x) ≫ e.inv
  map_add' x y := by
    change e.hom ≫ natTrans ((selfInt.intertwines x).add (selfInt.intertwines y)) ≫ e.inv = _
    rw [natTrans_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' c x := by
    change e.hom ≫ natTrans ((selfInt.intertwines x).smul c) ≫ e.inv = _
    rw [natTrans_smul, Linear.smul_comp, Linear.comp_smul]
    rfl

theorem endHom_apply (e : G ≅ functor.{u, w} Φ) (x : selfInt k Φ) :
    endHom e x = e.hom ≫ natTrans (selfInt.intertwines x) ≫ e.inv := rfl

theorem endHom_one (e : G ≅ functor.{u, w} Φ) : endHom (k := k) e 1 = 1 := by
  rw [endHom_apply]
  have h1 : natTrans.{u, w} (selfInt.intertwines (1 : selfInt k Φ)) =
      natTrans (Intertwines.unit Φ) :=
    natTrans_eq_of_unit_mul _ _ (by
      change Φ 1 * 1 = Φ 1 * Φ 1
      rw [← map_mul, mul_one, mul_one])
  rw [h1, natTrans_unit, Category.id_comp, Iso.hom_inv_id]
  rfl

theorem endHom_mul (e : G ≅ functor.{u, w} Φ) (x y : selfInt k Φ) :
    endHom e (x * y) = endHom e y * endHom e x := by
  rw [endHom_apply, End.mul_def, endHom_apply, endHom_apply]
  change _ = (e.hom ≫ natTrans (selfInt.intertwines x) ≫ e.inv) ≫
    e.hom ≫ natTrans (selfInt.intertwines y) ≫ e.inv
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (natTrans _) (natTrans _) e.inv, natTrans_comp]

/-- Polynomials in represented endomorphisms are represented by the polynomial in the
elements, with the variables read in the opposite order. -/
theorem endHom_ncEval (e : G ≅ functor.{u, w} Φ) {n : ℕ} (y : Fin n → selfInt k Φ)
    (p : MvPolynomial (Fin n) k) :
    endHom e (KLR.ncEval y p) =
      KLR.ncEval (fun a => endHom e (y (Fin.rev a))) (MvPolynomial.rename Fin.rev p) :=
  KLR.ncEval_antihom (endHom e) (endHom_one e) (endHom_mul e) y p

end

end Categorification.InductionAlong
