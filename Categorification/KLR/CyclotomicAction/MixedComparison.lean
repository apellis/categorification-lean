/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.Comparison
import Categorification.KLR.CyclotomicMixedMate.BicategoricalInversion
import Categorification.TwoRep.MateNat


/-!
# The mixed crossing of cyclotomic induction

For `i ≠ j` the crossing `cross : F_i F_j ⟶ F_j F_i` of `CyclotomicAction` lands in modules over
`R^Λ(γ + α_j + α_i)`, written with the weight `{i} + ({j} + γ)`. The library's blockwise mixed
mate (`KLRAlgebra.AbsentColour.BicategoricalMixedMate.actualMate`) lands instead in modules over
`R^Λ({j} + ({i} + γ))`, transported along the weight isomorphism `κ`
(`MixedMate.upperTransport`). This file identifies the two:

* `upperIso`: induction along `lastEmb j h₄` is cyclotomic induction followed by `κ`;
* `mixed_cross_compat`: under `indIso` and `upperIso`, `cross` is minus the crossing
  `crossingNat`.

Consequently the mate `E_i F_j ⟶ F_j E_i` of `cross` along the induction–restriction
adjunctions is invertible on each block (`mixedMate_isIso`; Brundan, arXiv:1501.00350v1, (1.7),
and the case `i ≠ j` of Kang–Kashiwara, arXiv:1102.4677v4, Theorem 5.2).
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory MulOpposite KLRAlgebra.AbsentColour
open scoped ModuleCat.Algebra

universe u v w

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k) (γ : Multiset I) (i j : I)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Sj" => (Singleton.singleton j : Multiset I)

theorem castCyc_eq_weightEquiv {β δ : Multiset I} (h h' : β = δ) :
    castCyc Q a h = MixedTransport.weightEquiv Q a h' := by
  subst h
  rfl

theorem lastEmb_upper (h₄ : Sj + (Si + γ) = Si + (Sj + γ)) (r : CycKLR k Q a (Si + γ)) :
    lastEmb Q a j h₄ r = MixedMate.κ Q a γ i j (cyclotomicLast Q j a (Si + γ) r) := by
  change castCyc Q a h₄ _ = MixedTransport.weightEquiv Q a (MixedCrossing.square γ i j) _
  rw [castCyc_eq_weightEquiv Q a h₄ (MixedCrossing.square γ i j)]

namespace UpperComparison

/-- The corners agree after the weight transport `κ`. -/
def cornerTo (h₄ : Sj + (Si + γ) = Si + (Sj + γ)) (z : InductionAlong.Corner (lastEmb Q a j h₄)) :
    IndCorner Q j a (Si + γ) :=
  ⟨(MixedMate.κ Q a γ i j).symm z.1, by
    have hz : z.1 * MixedMate.κ Q a γ i j (cyclotomicLast Q j a (Si + γ) 1) = z.1 :=
      (congrArg (z.1 * ·) (lastEmb_upper Q a γ i j h₄ 1)).symm.trans z.2
    apply (MixedMate.κ Q a γ i j).injective
    exact (map_mul _ _ _).trans
      ((congrArg (· * _) (AlgEquiv.apply_symm_apply _ _)).trans
        (hz.trans (AlgEquiv.apply_symm_apply _ _).symm))⟩

/-- The inverse corner map. -/
def cornerFrom (h₄ : Sj + (Si + γ) = Si + (Sj + γ)) (z : IndCorner Q j a (Si + γ)) :
    InductionAlong.Corner (lastEmb Q a j h₄) :=
  ⟨MixedMate.κ Q a γ i j z.1, by
    have hz : z.1 * cyclotomicLast Q j a (Si + γ) 1 = z.1 := z.2
    exact (congrArg (_ * ·) (lastEmb_upper Q a γ i j h₄ 1)).trans
      ((map_mul (MixedMate.κ Q a γ i j) _ _).symm.trans (congrArg _ hz))⟩

theorem cornerTo_op (h₄ : Sj + (Si + γ) = Si + (Sj + γ))
    (z : InductionAlong.Corner (lastEmb Q a j h₄)) (r : CycKLR k Q a (Si + γ)) :
    cornerTo Q a γ i j h₄ (op r • z) = op r • cornerTo Q a γ i j h₄ z :=
  Subtype.ext (by
    change (MixedMate.κ Q a γ i j).symm (z.1 * lastEmb Q a j h₄ r) =
      (MixedMate.κ Q a γ i j).symm z.1 * cyclotomicLast Q j a (Si + γ) r
    rw [lastEmb_upper Q a γ i j h₄ r, map_mul, AlgEquiv.symm_apply_apply])

theorem cornerFrom_op (h₄ : Sj + (Si + γ) = Si + (Sj + γ))
    (z : IndCorner Q j a (Si + γ)) (r : CycKLR k Q a (Si + γ)) :
    cornerFrom Q a γ i j h₄ (op r • z) = op r • cornerFrom Q a γ i j h₄ z :=
  Subtype.ext (by
    change MixedMate.κ Q a γ i j (z.1 * cyclotomicLast Q j a (Si + γ) r) =
      MixedMate.κ Q a γ i j z.1 * lastEmb Q a j h₄ r
    rw [lastEmb_upper Q a γ i j h₄ r, map_mul])

variable (M : ModuleCat.{max (max u v) w} (CycKLR k Q a ({i} + γ)))

/-- Induction along the transported last-strand embedding, compared with the original
induction followed by the weight transport. -/
def toUpper (h₄ : Sj + (Si + γ) = Si + (Sj + γ)) :
    (ind.{u, v, w} Q a j h₄).obj M →ₗ[CycKLR k Q a (Si + (Sj + γ))]
      (MixedMate.upperTransport.{u, v, w} Q a γ i j).obj
        ((inductionFunctor.{u, v, w} Q j a (Si + γ)).obj M) :=
  InductionAlong.Ind.lift
    (fun z m => (BalancedTensor.tmul (cornerTo Q a γ i j h₄ z) m :
      Ind Q j a (Si + γ) M))
    (fun z z' m => by
      rw [show cornerTo Q a γ i j h₄ (z + z') = cornerTo Q a γ i j h₄ z +
        cornerTo Q a γ i j h₄ z' from Subtype.ext (map_add _ _ _)]
      exact BalancedTensor.add_tmul _ _ m)
    (fun _ m m' => BalancedTensor.tmul_add _ m m')
    (fun z r m => by
      rw [cornerTo_op]
      exact BalancedTensor.op_smul_tmul _ r m)
    (fun s z m => by
      change _ = (MixedMate.κ Q a γ i j).symm s • (BalancedTensor.tmul _ m :
        Ind Q j a (Si + γ) M)
      rw [BalancedTensor.smul_tmul']
      congr 1
      exact Subtype.ext (map_mul _ _ _))

@[simp] theorem toUpper_tmul (h₄ : Sj + (Si + γ) = Si + (Sj + γ))
    (z : InductionAlong.Corner (lastEmb Q a j h₄)) (m : M) :
    toUpper Q a γ i j M h₄ (InductionAlong.Ind.tmul z m) =
      (BalancedTensor.tmul (cornerTo Q a γ i j h₄ z) m : Ind Q j a (Si + γ) M) := rfl

theorem corner_algebraMap (h₄ : Sj + (Si + γ) = Si + (Sj + γ))
    (y : CycKLR k Q a (Si + (Sj + γ)))
    (hy : y * lastEmb Q a j h₄ 1 = y) (c : k) :
    y * lastEmb Q a j h₄ (algebraMap k (CycKLR k Q a (Si + γ)) c) =
      algebraMap k (CycKLR k Q a (Si + (Sj + γ))) c * y := by
  rw [lastEmb_upper Q a γ i j h₄] at hy ⊢
  rw [Algebra.algebraMap_eq_smul_one c, map_smul, map_smul, mul_smul_comm, hy,
    ← Algebra.smul_def]

/-- The inverse comparison. -/
def fromUpper (h₄ : Sj + (Si + γ) = Si + (Sj + γ)) :
    Ind Q j a (Si + γ) M →ₗ[k] (ind.{u, v, w} Q a j h₄).obj M :=
  BalancedTensor.lift
    (LinearMap.mk₂ k (fun (z : IndCorner Q j a (Si + γ)) (m : M) =>
      (InductionAlong.Ind.tmul (cornerFrom Q a γ i j h₄ z) m : (ind Q a j h₄).obj M))
      (fun z z' m => by
        rw [show cornerFrom Q a γ i j h₄ (z + z') = cornerFrom Q a γ i j h₄ z +
          cornerFrom Q a γ i j h₄ z' from Subtype.ext (map_add _ _ _)]
        exact InductionAlong.Ind.add_tmul _ _ m)
      (fun c z m => by
        change _ = (algebraMap k (CycKLR k Q a (Si + (Sj + γ))) c •
          (InductionAlong.Ind.tmul (cornerFrom Q a γ i j h₄ z) m :
            InductionAlong.Ind M (lastEmb Q a j h₄)))
        rw [InductionAlong.Ind.smul_tmul]
        congr 1
        refine Subtype.ext ?_
        change MixedMate.κ Q a γ i j (c • z.1) = _
        rw [map_smul, Algebra.smul_def]
        rfl)
      (fun z m m' => InductionAlong.Ind.tmul_add _ m m')
      (fun c z m => by
        change InductionAlong.Ind.tmul _ (algebraMap k (CycKLR k Q a (Si + γ)) c • m) =
          (algebraMap k (CycKLR k Q a (Si + (Sj + γ))) c •
            (InductionAlong.Ind.tmul (cornerFrom Q a γ i j h₄ z) m :
              InductionAlong.Ind M (lastEmb Q a j h₄)))
        rw [← InductionAlong.Ind.op_smul_tmul, InductionAlong.Ind.smul_tmul]
        congr 1
        refine Subtype.ext ?_
        change (cornerFrom Q a γ i j h₄ z).1 * lastEmb Q a j h₄
          (algebraMap k (CycKLR k Q a (Si + γ)) c) =
          algebraMap k (CycKLR k Q a (Si + (Sj + γ))) c * (cornerFrom Q a γ i j h₄ z).1
        exact corner_algebraMap Q a γ i j h₄ _ (cornerFrom Q a γ i j h₄ z).2 c))
    (fun z r m => by
      change InductionAlong.Ind.tmul (cornerFrom Q a γ i j h₄ (op r • z)) m = _
      rw [cornerFrom_op]
      exact InductionAlong.Ind.op_smul_tmul _ r m)

/-- **Induction along the transported embedding is the original induction followed by the weight
transport.** -/
def upperEquiv (h₄ : Sj + (Si + γ) = Si + (Sj + γ)) :
    (ind.{u, v, w} Q a j h₄).obj M ≃ₗ[CycKLR k Q a (Si + (Sj + γ))]
      (MixedMate.upperTransport.{u, v, w} Q a γ i j).obj
        ((inductionFunctor.{u, v, w} Q j a (Si + γ)).obj M) :=
  { toUpper Q a γ i j M h₄ with
    invFun := fromUpper Q a γ i j M h₄
    left_inv := fun x => by
      induction x using InductionAlong.Ind.induction_on with
      | zero => exact (congrArg _ (map_zero _)).trans (map_zero _)
      | tmul z m =>
        exact congrArg (fun z' => (InductionAlong.Ind.tmul z' m : (ind Q a j h₄).obj M))
          (Subtype.ext (AlgEquiv.apply_symm_apply _ _))
      | add s t hs ht =>
        have hs' : fromUpper Q a γ i j M h₄ (toUpper Q a γ i j M h₄ s) = s := hs
        have ht' : fromUpper Q a γ i j M h₄ (toUpper Q a γ i j M h₄ t) = t := ht
        exact ((congrArg (fromUpper Q a γ i j M h₄) ((toUpper Q a γ i j M h₄).map_add s t)).trans
          ((fromUpper Q a γ i j M h₄).map_add _ _)).trans (by rw [hs', ht']; rfl)
    right_inv := fun x => by
      induction x using BalancedTensor.induction_on with
      | zero => exact (congrArg _ (map_zero _)).trans (map_zero _)
      | tmul z m =>
        exact congrArg (fun z' => (BalancedTensor.tmul z' m : Ind Q j a (Si + γ) M))
          (Subtype.ext (AlgEquiv.symm_apply_apply _ _))
      | add s t hs ht =>
        have hs' : toUpper Q a γ i j M h₄ (fromUpper Q a γ i j M h₄ s) = s := hs
        have ht' : toUpper Q a γ i j M h₄ (fromUpper Q a γ i j M h₄ t) = t := ht
        exact ((congrArg (toUpper Q a γ i j M h₄) ((fromUpper Q a γ i j M h₄).map_add s t)).trans
          ((toUpper Q a γ i j M h₄).map_add _ _)).trans (by rw [hs', ht']; rfl) }

end UpperComparison

open UpperComparison

/-- **Induction along the transported last-strand embedding** is induction followed by the
weight transport `κ`. -/
def upperIso (h₄ : Sj + (Si + γ) = Si + (Sj + γ)) :
    ind.{u, v, w} Q a j h₄ ≅
      inductionFunctor.{u, v, w} Q j a (Si + γ) ⋙ MixedMate.upperTransport Q a γ i j :=
  NatIso.ofComponents (fun M => (upperEquiv Q a γ i j M h₄).toModuleIso)
    (fun _ => ModuleCat.hom_ext (InductionAlong.Ind.ext fun _ _ => rfl))

/-- **The mixed crossing of `ind` is minus the crossing of the induction functors**, transported
along `indIso` and `upperIso`. -/
theorem mixed_cross_compat (h₄ : Sj + (Si + γ) = Si + (Sj + γ)) :
    cross.{u, v, w} Q a i j (rfl : Sj + γ = Sj + γ) (rfl : Si + (Sj + γ) = Si + (Sj + γ))
        (rfl : Si + γ = Si + γ) h₄ ≫
      (Functor.whiskerRight (indIso Q a i γ).hom (ind Q a j h₄) ≫
        Functor.whiskerLeft (inductionFunctor Q i a γ) (-(upperIso Q a γ i j h₄).hom)) =
    (Functor.whiskerRight (indIso Q a j γ).hom (ind Q a i rfl) ≫
        Functor.whiskerLeft (inductionFunctor Q j a γ) (indIso Q a i (Sj + γ)).hom) ≫
      BicategoricalMixedMate.crossingNat Q a γ i j := by
  ext N : 2
  refine ModuleCat.hom_ext (InductionAlong.Ind.ext₂ fun z w n => ?_)
  change -(BalancedTensor.tmul (cornerTo Q a γ i j h₄
      ⟨z.1 * lastEmb Q a i (rfl : Si + (Sj + γ) = _) w.1 *
        crossElt Q a (γ := γ) (δ := Si + (Sj + γ)), _⟩)
      (BalancedTensor.tmul ⟨lastEmb Q a i (rfl : Si + γ = _) 1, _⟩ n) :
        Ind Q j a (Si + γ) (Ind Q i a γ N)) =
    MixedMate.crossing Q a γ i j N
      (BalancedTensor.tmul ⟨z.1, z.2⟩ (BalancedTensor.tmul ⟨w.1, w.2⟩ n))
  rw [MixedMate.crossing_tmul_explicit]
  set X : Ind Q i a γ N := BalancedTensor.tmul (indGenerator Q i a γ) n
  have key : ∀ c d : IndCorner Q j a (Si + γ),
      d.1 = -(c.1 * cyclotomicLast Q j a (Si + γ) (lastIdem Q i a γ)) →
        (BalancedTensor.tmul d X : Ind Q j a (Si + γ) (Ind Q i a γ N)) =
          -BalancedTensor.tmul c X := by
    intro c d hd
    have hd' : d = -(op (lastIdem Q i a γ) • c) := Subtype.ext hd
    have hX : lastIdem Q i a γ • X = X := by
      rw [BalancedTensor.smul_tmul', indGenerator_fixed]
    rw [hd']
    have hneg : ∀ e : IndCorner Q j a (Si + γ),
        (BalancedTensor.tmul (-e) X : Ind Q j a (Si + γ) (Ind Q i a γ N)) =
          -BalancedTensor.tmul e X := fun e =>
      eq_neg_of_add_eq_zero_left (by
        rw [← BalancedTensor.add_tmul, neg_add_cancel, BalancedTensor.zero_tmul])
    rw [hneg, BalancedTensor.op_smul_tmul, hX]
  refine (key _ _ ?_).symm
  change (MixedMate.κ Q a γ i j).symm (z.1 * cyclotomicLast Q i a (Sj + γ) w.1 *
      MixedMate.coefficient Q a γ i j) =
    -((MixedMate.κ Q a γ i j).symm (z.1 * cyclotomicLast Q i a (Sj + γ) w.1 *
      CycKLR.mk k Q a _ (KLRAlgebra.ψ (Multiset.card γ))) *
        cyclotomicLast Q j a (Si + γ) (lastIdem Q i a γ))
  rw [MixedMate.coefficient_eq, neg_mul, mul_neg, map_neg, ← mul_assoc, map_mul,
    AlgEquiv.symm_apply_apply]
  rfl

open TwoRep BicategoricalMixedMate in
/-- **The mixed sideways crossing `E_i F_j → F_j E_i` is invertible on each block** for `i ≠ j`
(Brundan, arXiv:1501.00350v1, (1.7); Kang–Kashiwara, arXiv:1102.4677v4, Theorem 5.2). -/
theorem mixedMate_isIso (hij : i ≠ j) (hsym : KLRSymm Q)
    (h₄ : Sj + (Si + γ) = Si + (Sj + γ)) :
    IsIso (mateNat (indResAdj.{u, v, w} Q a i (rfl : Si + (Sj + γ) = Si + (Sj + γ))).unit
      (cross Q a i j (rfl : Sj + γ = Sj + γ) (rfl : Si + (Sj + γ) = Si + (Sj + γ))
        (rfl : Si + γ = Si + γ) h₄)
      (indResAdj Q a i (rfl : Si + γ = Si + γ)).counit) := by
  have hA : IsIso (mateNat (cyclotomicAdjunction.{u, v, w} Q i a (Sj + γ)).unit
      (crossingNat Q a γ i j) (cyclotomicAdjunction Q i a γ).counit) := by
    have h3 : IsIso ((ObjectProperty.ι _).map (actualMate.{u, v, w} Q a γ i j)) :=
      haveI := actualMate_isIso Q a γ i j hij hsym
      inferInstance
    change IsIso (actualMate.{u, v, w} Q a γ i j).hom at h3
    rw [actualMate, AdditiveCat.mate_hom] at h3
    exact h3
  let hN : ind.{u, v, w} Q a j h₄ ≅
      inductionFunctor Q j a (Si + γ) ⋙ MixedMate.upperTransport Q a γ i j :=
    { hom := -(upperIso Q a γ i j h₄).hom
      inv := -(upperIso Q a γ i j h₄).inv
      hom_inv_id := by rw [Preadditive.neg_comp_neg, Iso.hom_inv_id]
      inv_hom_id := by rw [Preadditive.neg_comp_neg, Iso.inv_hom_id] }
  exact isIso_mateNat_of_conj _ _ _ _ _ _ (indIso Q a i γ) (resIso Q a i γ) (indIso Q a j γ)
    (indIso Q a i (Sj + γ)) (resIso Q a i (Sj + γ)) hN (unit_compat_nat Q a i (Sj + γ))
    (counit_compat_nat Q a i γ) (mixed_cross_compat Q a γ i j h₄)

end

end Categorification.KLR.CyclotomicAction
