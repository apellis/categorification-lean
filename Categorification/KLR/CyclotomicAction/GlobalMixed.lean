/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.GlobalFamily
import Categorification.KLR.CyclotomicAction.MixedComparison
import Categorification.TwoRep.RouqFullCL


/-!
# Mixed inversion for the cyclotomic Rouquier family

For `i ≠ j`, Brundan's mixed sideways crossing `E_i F_j ⟶ F_j E_i` (arXiv:1501.00350v1, (1.7);
`TwoRep.RouqFamily.mixedSigma`) of the weight-indexed cyclotomic family `cyclotomicFamily` is
invertible (`cyclotomicFamily_mixedInversion`). This is the case `i ≠ j` of Kang–Kashiwara
(arXiv:1102.4677v4, Theorem 5.2) on weight spaces.

The crossing on weight spaces is block diagonal (`mixedSigma_app`). On a block `{j} + γ` it is
the blockwise mixed mate at `{i} + γ` (`mixedMate_isIso`), conjugated by the inclusions of single
summands. On a block without a strand of colour `j`, its source and target are zero.
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory TwoRep QuantumGroup
  KLRAlgebra.AbsentColour

universe u v w u₁

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)

/-- `mixedMate_isIso` for arbitrary block equalities. -/
theorem mixedMate_isIso_of_eq (i j : I) (hij : i ≠ j) (hsym : KLRSymm Q)
    {γ β β' δ : Multiset I} (h₁ : {j} + γ = β) (h₂ : {i} + β = δ) (h₃ : {i} + γ = β')
    (h₄ : {j} + β' = δ) :
    IsIso (mateNat (indResAdj.{u, v, w} Q a i h₂).unit (cross Q a i j h₁ h₂ h₃ h₄)
      (indResAdj Q a i h₃).counit) := by
  subst h₁ h₂ h₃
  exact mixedMate_isIso Q a γ i j hij hsym h₄

variable {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.WeightDatum C X Y) (Λ : X)

/-- The generator of `E_j E_i` on `F_i E_i`, followed by the counit, for any target block. -/
theorem gen₂_counit_of_eq (i j : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX j = z)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (γ : WeightBlocks RD Λ x) {δ : WeightBlocks RD Λ z}
    (hd : blockSucc RD Λ j h₂ (blockSucc RD Λ i h₁ γ) = δ) :
    Eq (gen₂ (blockSucc RD Λ i h₁) (blockSucc RD Λ j h₂) (indBlock.{u, v, w} Q a RD Λ i h₁)
        (indBlock Q a RD Λ j h₂) ((blockRes (blockSucc RD Λ i h₁) (resBlock Q a RD Λ i h₁)).obj M)
        γ rfl hd ≫
      (blockSum (blockSucc RD Λ j h₂) (indBlock Q a RD Λ j h₂)).map
        ((blockCounitNat (blockSucc RD Λ i h₁)
          (fun _ _ hβ => indResAdj.{u, v, w} Q a i (blockSucc_eq RD Λ i hβ))).app M) δ)
      ((indBlock Q a RD Λ j h₂ (blockSucc RD Λ i h₁ γ) δ hd).map
          ((indResAdj Q a i (blockSucc_step RD Λ i h₁ γ)).counit.app
            (M (blockSucc RD Λ i h₁ γ))) ≫
        blockι (blockSucc RD Λ j h₂) (indBlock Q a RD Λ j h₂) M ⟨blockSucc RD Λ i h₁ γ, hd⟩) := by
  subst hd
  rw [gen₂, Category.assoc, blockι_map, ← Category.assoc, ← Functor.map_comp]
  congr 2
  exact biproduct.ι_desc _ _

/-- **The mixed sideways crossing on weight spaces, blockwise**: on the generator of `F_i E_j` at
the block `{j} + γ`, it is the mixed mate of the cyclotomic block functors at `{i} + γ`, followed
by the generator of `E_j F_i`. -/
theorem mixedSigma_app (i j : I) {x y z t : X} (hj : x + RD.iX j = y) (hi' : y + RD.iX i = t)
    (hi : x + RD.iX i = z) (hj' : z + RD.iX j = t)
    (M : ∀ β : WeightBlocks RD Λ z, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (γ : WeightBlocks RD Λ x) :
    Eq (blockι (blockSucc RD Λ j hj) (indBlock.{u, v, w} Q a RD Λ j hj)
        ((blockRes (blockSucc RD Λ i hi) (resBlock Q a RD Λ i hi)).obj M) ⟨γ, rfl⟩ ≫
      (mateNat (globalAdj Q a RD Λ i hi').unit.hom
        (globalCross Q a RD Λ i j hj hi' hi hj').hom
        (globalAdj Q a RD Λ i hi).counit.hom).app M (blockSucc RD Λ j hj γ))
      ((mateNat (indResAdj Q a i (blockSucc_step RD Λ i hi' (blockSucc RD Λ j hj γ))).unit
          (signedCross Q a i j (blockSucc_step RD Λ j hj γ)
            (blockSucc_step RD Λ i hi' (blockSucc RD Λ j hj γ)) (blockSucc_step RD Λ i hi γ)
            (blockSucc_eq RD Λ j (blockSucc_comm RD Λ i j hj hi' hi hj' γ).symm))
          (indResAdj Q a i (blockSucc_step RD Λ i hi γ)).counit).app
          (M (blockSucc RD Λ i hi γ)) ≫
        (resBlock Q a RD Λ i hi' (blockSucc RD Λ j hj γ) _ rfl).map
          (blockι (blockSucc RD Λ j hj') (indBlock Q a RD Λ j hj') M
            ⟨blockSucc RD Λ i hi γ, (blockSucc_comm RD Λ i j hj hi' hi hj' γ).symm⟩)) := by
  have hU := (indResAdj.{u, v, w} Q a i
    (blockSucc_step RD Λ i hi' (blockSucc RD Λ j hj γ))).unit_naturality
    (blockι (blockSucc RD Λ j hj) (indBlock.{u, v, w} Q a RD Λ j hj)
        ((blockRes (blockSucc RD Λ i hi) (resBlock Q a RD Λ i hi)).obj M) ⟨γ, rfl⟩)
  have hT := gen₂_globalCross Q a RD Λ i j hj hi' hi hj'
    ((blockRes (blockSucc RD Λ i hi) (resBlock Q a RD Λ i hi)).obj M) γ rfl rfl rfl
    (blockSucc_comm RD Λ i j hj hi' hi hj' γ).symm
  have hC := gen₂_counit_of_eq Q a RD Λ i j hi hj' M γ
    (blockSucc_comm RD Λ i j hj hi' hi hj' γ).symm
  have key := (Category.assoc _ _ _).symm.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) hT).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hC))))
  change blockι (blockSucc RD Λ j hj) (indBlock.{u, v, w} Q a RD Λ j hj)
        ((blockRes (blockSucc RD Λ i hi) (resBlock Q a RD Λ i hi)).obj M) ⟨γ, rfl⟩ ≫
      (((indResAdj.{u, v, w} Q a i (blockSucc_step RD Λ i hi' (blockSucc RD Λ j hj γ))).unit.app
          ((blockSum (blockSucc RD Λ j hj) (indBlock Q a RD Λ j hj)).obj
            ((blockRes (blockSucc RD Λ i hi) (resBlock Q a RD Λ i hi)).obj M)
              (blockSucc RD Λ j hj γ)) ≫
        (res Q a i (blockSucc_step RD Λ i hi' (blockSucc RD Λ j hj γ))).map
          (blockι (blockSucc RD Λ i hi') (indBlock Q a RD Λ i hi')
            ((blockSum (blockSucc RD Λ j hj) (indBlock Q a RD Λ j hj)).obj
              ((blockRes (blockSucc RD Λ i hi) (resBlock Q a RD Λ i hi)).obj M))
            ⟨blockSucc RD Λ j hj γ, rfl⟩)) ≫
        (res Q a i (blockSucc_step RD Λ i hi' (blockSucc RD Λ j hj γ))).map
          ((globalCross Q a RD Λ i j hj hi' hi hj').hom.app
            ((blockRes (blockSucc RD Λ i hi) (resBlock Q a RD Λ i hi)).obj M)
            (blockSucc RD Λ i hi' (blockSucc RD Λ j hj γ)))) ≫
      (res Q a i (blockSucc_step RD Λ i hi' (blockSucc RD Λ j hj γ))).map
        ((blockSum (blockSucc RD Λ j hj') (indBlock Q a RD Λ j hj')).map
          ((blockCounitNat (blockSucc RD Λ i hi)
            (fun _ _ hβ => indResAdj.{u, v, w} Q a i (blockSucc_eq RD Λ i hβ))).app M)
          (blockSucc RD Λ i hi' (blockSucc RD Λ j hj γ))) = _
  simp only [Category.assoc]
  erw [← reassoc_of% hU]
  erw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  have key' := congrArg (res Q a i (blockSucc_step RD Λ i hi' (blockSucc RD Λ j hj γ))).map key
  erw [key']
  simp only [Functor.map_comp]
  rfl

section Family

variable {Q a}
  (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

/-- **Brundan's mixed inversion for the cyclotomic family** (Brundan, arXiv:1501.00350v1, (1.7);
Kang–Kashiwara, arXiv:1102.4677v4, Theorem 5.2 for `i ≠ j`). -/
theorem cyclotomicFamily_mixedInversion :
    BrundanMixedInversion (cyclotomicFamily.{u, v, w} hQ hlead ha RD Λ hΛ hdeg) := by
  intro i j hij x y z t hj hi' hi hj'
  change IsIso (mateEquiv (globalAdj.{u, v, w} Q a RD Λ i hi) (globalAdj Q a RD Λ i hi')
    (globalCross Q a RD Λ i j hj hi' hi hj'))
  suffices h : IsIso ((LinearCat.homForget _ _).map
      (mateEquiv (globalAdj.{u, v, w} Q a RD Λ i hi) (globalAdj Q a RD Λ i hi')
        (globalCross Q a RD Λ i j hj hi' hi hj'))) from
    isIso_of_fully_faithful (LinearCat.homForget _ _) _
  rw [LinearCat.homForget_map, LinearCat.mate_hom]
  refine (NatTrans.isIso_iff_isIso_app _).2 fun M => ?_
  refine (isIso_pi_iff _).2 fun β => ?_
  by_cases hβ : j ∈ β.1
  · obtain ⟨γ, rfl⟩ := exists_blockSucc_of_mem RD Λ j hj β hβ
    have e := mixedSigma_app Q a RD Λ i j hj hi' hi hj' M γ
    rw [signedCross_of_ne Q a hij] at e
    have := mixedMate_isIso_of_eq.{u, v, w} Q a i j hij hQ (blockSucc_step RD Λ j hj γ)
      (blockSucc_step RD Λ i hi' (blockSucc RD Λ j hj γ)) (blockSucc_step RD Λ i hi γ)
      (blockSucc_eq RD Λ j (blockSucc_comm RD Λ i j hj hi' hi hj' γ).symm)
    let e₁ := blockιIso (blockSucc RD Λ j hj) (indBlock.{u, v, w} Q a RD Λ j hj)
      ((blockRes (blockSucc RD Λ i hi) (resBlock Q a RD Λ i hi)).obj M) ⟨γ, rfl⟩
      (fun _ => Subsingleton.elim _ _)
    let e₂ := blockιIso (blockSucc RD Λ j hj') (indBlock.{u, v, w} Q a RD Λ j hj') M
      ⟨blockSucc RD Λ i hi γ, (blockSucc_comm RD Λ i j hj hi' hi hj' γ).symm⟩
      (fun _ => Subsingleton.elim _ _)
    have e' := (Iso.eq_inv_comp e₁).2 e
    erw [e']
    refine IsIso.comp_isIso' e₁.isIso_inv (IsIso.comp_isIso' ?_ ?_)
    · exact NatIso.isIso_app_of_isIso _ _
    · exact ((resBlock Q a RD Λ i hi' (blockSucc RD Λ j hj γ) _ rfl).mapIso e₂).isIso_hom
  · refine isIso_of_source_target_iso_zero _
      (IsZero.isoZero (blockSum_obj_isZero (blockSucc RD Λ j hj) (indBlock.{u, v, w} Q a RD Λ j hj)
        _ (isEmpty_of_not_mem RD Λ j hj β hβ)))
      (IsZero.isoZero (Functor.map_isZero (resBlock Q a RD Λ i hi' β _ rfl)
        (blockSum_obj_isZero (blockSucc RD Λ j hj') (indBlock.{u, v, w} Q a RD Λ j hj') M
          (isEmpty_of_not_mem RD Λ j hj' _ ?_))))
    rw [blockSucc_val]
    intro hm
    rcases Multiset.mem_add.1 hm with h | h
    · exact hij.symm (Multiset.mem_singleton.1 h)
    · exact hβ h

end Family

end

end Categorification.KLR.CyclotomicAction
