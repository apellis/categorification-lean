/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqProductLeft
import Categorification.TwoRep.FurlingKLR
import Categorification.KLR.Examples.Small

/-!
# Evaluating the Yoneda family

Let `S` be a Rouquier family in `LinearCat k`, and `y` a `k`-linear category. The family
`S.yoneda k y` of postcomposition has objects the functor categories `y ⟶ S(x)`. Evaluating its
words, dots and crossings first at a functor `V : y ⟶ S(μ)` and then at an object `v` of `y`
gives the words, dots and crossings of `S` evaluated at the object `V(v)` of `S(μ)`. Hence the
action of the KLR algebra `R(ν)` on the words of `S.yoneda k y`, evaluated at `V` and `v`, is the
action on the words of `S` evaluated at `V(v)` (`klrAct_yoneda_eval`).

This is the step from the left colours of a product family (`klrActAt_reindex_inl`) to the
family itself, used for the action of `R(ν)` on the vacuum vector in B. Webster, *Unfurling
Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of Theorem `nondegenerate`.

## Main declarations

* `RouqFamily.yEval`: evaluation of the 2-morphisms of `S.yoneda k y` at `V` and `z`;
* `RouqFamily.wcell_yoneda_eval`, `wdot_yoneda_eval`, `wcross_yoneda_eval`: words, dots and
  crossings;
* `RouqFamily.klrAct_yoneda_eval`: the action of the KLR algebra.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory

universe w' v u u₁

namespace LinearCat

variable {k : Type w'} [CommRing k] {C D E F : LinearCat.{w', v, u} k}

/-- The components of the associator of `LinearCat k` are identities. -/
@[simp] theorem associator_hom_hom_app (f : C ⟶ D) (g : D ⟶ E) (h : E ⟶ F) (x : (C : Type u)) :
    (α_ f g h).hom.hom.app x = 𝟙 _ := rfl

/-- The components of the inverse associator of `LinearCat k` are identities. -/
@[simp] theorem associator_inv_hom_app (f : C ⟶ D) (g : D ⟶ E) (h : E ⟶ F) (x : (C : Type u)) :
    (α_ f g h).inv.hom.app x = 𝟙 _ := rfl

end LinearCat

namespace RouqFamily

open QuantumGroup UDot KLR KLR.Diagram KLR.Diagram.MatEnd Yoneda TypeA

/-- A component of a natural transformation at an object `A`, conjugated to a component at an
equal object `A'`. -/
theorem app_eq_eqToHom_conj {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (η : F ⟶ G)
    {A A' : C} (q : A = A') (p : F.obj A = F.obj A') (p' : G.obj A = G.obj A') :
    η.app A = eqToHom p ≫ η.app A' ≫ eqToHom p'.symm := by
  subst q; simp


variable {k : Type w'} [CommRing k] {I : Type*} {C : CartanDatum I} {X Y : Type u₁}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  (S : RouqFamily (B := LinearCat.{w', v, u} k) RD) (y : LinearCat.{w', v, u} k) (μ : X)
  (V : y ⟶ S.obj μ) (z : (y : Type u))

/-- The word of a weighted word of `S.yoneda k y`, evaluated at `V` and `z`. -/
theorem wcell_yoneda_eval : ∀ (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ'),
    (((S.yoneda k y).wcell μ L μ' h).obj.obj V).obj.obj z =
      (S.wcell μ L μ' h).obj.obj (V.obj.obj z)
  | [], _, h => by subst h; rfl
  | (c, _) :: L, _, h => congrArg (S.E c h.2).obj.obj (wcell_yoneda_eval L _ h.1)

/-- The dots of `S.yoneda k y`, evaluated at `V` and `z`. -/
theorem wdot_yoneda_eval : ∀ (a : ℕ) (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ'),
    (((S.yoneda k y).wdot μ a L μ' h).hom.app V).hom.app z =
      eqToHom (S.wcell_yoneda_eval y μ V z L μ' h) ≫ (S.wdot μ a L μ' h).hom.app (V.obj.obj z) ≫
        eqToHom (S.wcell_yoneda_eval y μ V z L μ' h).symm
  | 0, (c, _) :: L, _, h =>
    app_eq_eqToHom_conj (S.dot c h.2).hom (S.wcell_yoneda_eval y μ V z L _ h.1)
      (congrArg _ (S.wcell_yoneda_eval y μ V z L _ h.1))
      (congrArg _ (S.wcell_yoneda_eval y μ V z L _ h.1))
  | a + 1, (c, _) :: L, _, h => by
    change (S.E c h.2).obj.map ((((S.yoneda k y).wdot μ a L _ h.1).hom.app V).hom.app z) = _
    rw [wdot_yoneda_eval a L _ h.1]
    simp [eqToHom_map]
    rfl
  | 0, [], _, _ => zero_eq_eqToHom_zero _ _
  | _ + 1, [], _, _ => zero_eq_eqToHom_zero _ _

/-- The crossings of `S.yoneda k y`, evaluated at `V` and `z`. -/
theorem wcross_yoneda_eval : ∀ (j : ℕ) (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ'),
    (((S.yoneda k y).wcross μ j L μ' h).hom.app V).hom.app z =
      eqToHom (S.wcell_yoneda_eval y μ V z L μ' h) ≫ (S.wcross μ j L μ' h).hom.app (V.obj.obj z) ≫
        eqToHom (S.wcell_yoneda_eval y μ V z (wswap RD j L) μ' (wValid_wswap j L h)).symm
  | 0, (c, _) :: (d, _) :: L, _, h => by
    simp only [RouqData.wcross]
    erw [LinearCat.comp_hom_app, LinearCat.comp_hom_app, LinearCat.comp_hom_app,
      LinearCat.comp_hom_app, LinearCat.comp_hom_app, LinearCat.comp_hom_app]
    erw [LinearCat.associator_hom_hom_app, LinearCat.associator_inv_hom_app,
      LinearCat.associator_hom_hom_app, LinearCat.associator_inv_hom_app]
    erw [Category.id_comp, Category.id_comp, Category.comp_id, Category.comp_id,
      Category.id_comp, Category.comp_id]
    exact app_eq_eqToHom_conj (S.cross c d _ _ _ _).hom (S.wcell_yoneda_eval y μ V z L _ h.1.1)
      (congrArg _ (S.wcell_yoneda_eval y μ V z L _ h.1.1))
      (congrArg _ (S.wcell_yoneda_eval y μ V z L _ h.1.1))
  | j + 1, (c, _) :: L, _, h => by
    change (S.E c h.2).obj.map ((((S.yoneda k y).wcross μ j L _ h.1).hom.app V).hom.app z) = _
    rw [wcross_yoneda_eval j L _ h.1]
    simp [eqToHom_map]
    rfl
  | 0, [], _, _ => zero_eq_eqToHom_zero _ _
  | 0, [_], _, _ => zero_eq_eqToHom_zero _ _
  | _ + 1, [], _, _ => zero_eq_eqToHom_zero _ _

section Words

variable {ν : Multiset I}

local notation "m" => Multiset.card ν

/-- The word of a sequence `t` of `S.yoneda k y`, evaluated at `V` and `z`. -/
theorem wordCell_yoneda_eval (t : Seq ν) :
    (((S.yoneda k y).wordCell μ t).obj.obj V).obj.obj z = (S.wordCell μ t).obj.obj (V.obj.obj z) :=
  S.wcell_yoneda_eval y μ V z _ _ _

/-- The dots on the word of `t` of `S.yoneda k y`, evaluated at `V` and `z`. -/
theorem wordDot_yoneda_eval (t : Seq ν) (a : Fin m) :
    (((S.yoneda k y).wordDot μ t a).hom.app V).hom.app z =
      eqToHom (S.wordCell_yoneda_eval y μ V z t) ≫ (S.wordDot μ t a).hom.app (V.obj.obj z) ≫
        eqToHom (S.wordCell_yoneda_eval y μ V z t).symm :=
  S.wdot_yoneda_eval y μ V z _ _ _ _

/-- The crossings on the word of `t` of `S.yoneda k y`, evaluated at `V` and `z`. -/
theorem wordCross_yoneda_eval (t : Seq ν) (j : ℕ) :
    (((S.yoneda k y).wordCross μ t j).hom.app V).hom.app z =
      eqToHom (S.wordCell_yoneda_eval y μ V z t) ≫ (S.wordCross μ t j).hom.app (V.obj.obj z) ≫
        eqToHom (S.wordCell_yoneda_eval y μ V z (sadj m j • t)).symm := by
  by_cases hj : j + 1 < m
  · rw [RouqData.wordCross_def _ _ _ hj, RouqData.wordCross_def _ _ _ hj, RouqData.wcrossTo,
      RouqData.wcrossTo]
    erw [LinearCat.comp_hom_app, LinearCat.comp_hom_app, LinearCat.eqToHom_hom_app,
      LinearCat.eqToHom_hom_app, LinearCat.eqToHom_hom_app]
    rw [wcross_yoneda_eval]
    simp
  · rw [RouqData.wordCross_of_le _ _ _ (by omega), RouqData.wordCross_of_le _ _ _ (by omega)]
    exact zero_eq_eqToHom_zero _ _

end Words

variable (k) in
/-- Evaluation of the 2-morphisms of `S.yoneda k y` at a functor `V : y ⟶ S(μ)` and then at an
object `z` of `y`. -/
@[simps] def yEval (μ' : X) :
    ((S.yoneda k y).obj μ ⟶ (S.yoneda k y).obj μ') ⥤ (S.obj μ' : Type u) where
  obj G := (G.obj.obj V).obj.obj z
  map η := (η.hom.app V).hom.app z

instance (μ' : X) : (yEval k S y μ V z μ').Additive where
  map_add := rfl

instance (μ' : X) : (yEval k S y μ V z μ').Linear k where
  map_smul _ _ := rfl

variable [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Q)
  (ν : Multiset I)

/-- **The action of `R(ν)` on the words of the Yoneda family, evaluated** at a functor
`V : y ⟶ S(μ)` and an object `z` of `y`, is the action on the words of `S` evaluated at `V(z)`,
conjugated along `wordCell_yoneda_eval`. -/
theorem klrAct_yoneda_eval :
    (mapAlg k (yEval k S y μ V z (wtop RD μ ν)) _).comp
        (klrAct (ν := ν) (yoneda_upKLR (k := k) S y H) μ) =
      (conjAlg k (Z := fun t => (yEval k S y μ V z (wtop RD μ ν)).obj
          ((S.yoneda k y).wordCell μ t))
          (Y := fun t => (LinearCat.evalAt (C := S.obj μ) (D := S.obj (wtop RD μ ν))
            (V.obj.obj z)).obj (S.wordCell μ t))
          (Equiv.refl (Seq ν)) (S.wordCell_yoneda_eval y μ V z)).comp
        ((mapAlg k (LinearCat.evalAt (C := S.obj μ) (D := S.obj (wtop RD μ ν))
          (V.obj.obj z)) _).comp
          (klrAct H μ)) := by
  refine KLRAlgebra.algHom_ext (fun t => ?_) (fun a => ?_) (fun j => ?_)
  · simp only [AlgHom.comp_apply, klrAct_e, RouqData.wordE_eq, mapAlg_single]
    erw [conjAlg_single (Equiv.refl (Seq ν)) _ t t]
    exact congrArg _ (eqToHom_id_eqToHom _ _).symm
  · simp only [AlgHom.comp_apply, klrAct_dot, RouqData.wordX, map_sum, mapAlg_single]
    refine Finset.sum_congr rfl fun t _ => ?_
    erw [conjAlg_single (Equiv.refl (Seq ν)) _ t t]
    exact congrArg _ (S.wordDot_yoneda_eval y μ V z t a)
  · simp only [AlgHom.comp_apply, klrAct_cross, RouqData.wordΨ, map_sum, mapAlg_single]
    refine Finset.sum_congr rfl fun t _ => ?_
    erw [conjAlg_single (Equiv.refl (Seq ν)) _ t (sadj (Multiset.card ν) j • t)]
    exact congrArg _ (S.wordCross_yoneda_eval y μ V z t j)

end RouqFamily

end Categorification.TwoRep
