/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingStack
import Categorification.Algebra.BalancedTensorAssoc
import Categorification.Algebra.BalancedTensorSplit

/-!
# Cutting at an uncrossed horizontal seam

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8. Given a juxtaposed upper diagram
and a global lower diagram, cut at their common boundary. Moving an ordered block diagram
across that seam does not change the balanced class. Stacking again inserts the uncrossed
block projector between the two diagrams. This calculation is on separated representatives;
it does not assume that the cut descends from all equalities of unmarked global diagrams.
-/

noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR MulOpposite BraidedStendhalAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)
    (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν)
local notation "Bs" => adjacentRow L M f β
local notation "botOrd" => (fun (_ : RedBlock I ℓ) => 1)
local notation "topOrd" => (fun (_ : RedBlock I ℓ) => Fin.revPerm)
local notation "D₀" => orderedProduct Q Λ botOrd Bs
local notation "D₁" => orderedProduct Q Λ topOrd Bs
local notation "ι₀" => orderedInclusion Q Λ hQ botOrd Bs
local notation "ι₁" => orderedInclusion Q Λ hQ topOrd Bs
local notation "C" => crossingProduct Q Λ hQ M f β L
local notation "S₀" => orderedColumn Q Λ hQ botOrd L M f β h
local notation "S₁" => orderedColumn Q Λ hQ topOrd L M f β h
local notation "Z" => BalancedTensor k D₁ D₀ (BlockCut.space C) S₀
local notation "F" => stackBlocks Q Λ L M f β h
local notation "V" => ViolQuotient k Q Λ ν
local notation "π" => projection Q Λ Bs
local notation "act" => blockProductAction Q Λ L M f β h
local notation "κ₀" => L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst
local notation "p" => violMk k Q Λ ν (redProj k Q Λ ν κ₀)
local notation "J" => blockUpperIdeal k Q Λ ν (f 0) (f 1) (fun r i => boundaryCount (cut (f 0) (f 1) r) i Bs) κ₀
local notation "q" => RingCon.mkₐ k (TwoSidedIdeal.ringCon J)
local notation "E₀" => orderedIdem Q Λ botOrd Bs
local notation "stk" => crossingStack Q Λ hQ L M f β h

local instance cutColumnAddGroup (σ : (B : RedBlock I ℓ) → Equiv.Perm (Fin B.size)) :
    AddCommGroup (orderedColumn Q Λ hQ σ L M f β h) := Submodule.addCommGroup _

private def columnRep : V →ₗ[k] blockColumn Q Λ L M f β h :=
  ((q).toLinearMap ∘ₗ LinearMap.mulLeft k (F 1) ∘ₗ LinearMap.mulRight k p).rangeRestrict

/-- Project a global representative to the column in the given top order. -/
def orderedColumnRep (σ : (B : RedBlock I ℓ) → Equiv.Perm (Fin B.size)) :
    V →ₗ[k] orderedColumn Q Λ hQ σ L M f β h :=
  (act (orderedInclusion Q Λ hQ σ Bs 1)).rangeRestrict ∘ₗ columnRep Q Λ L M f β h

local notation "rep₀" => orderedColumnRep Q Λ hQ L M f β h botOrd
local notation "rep₁" => orderedColumnRep Q Λ hQ L M f β h topOrd

theorem orderedColumnRep_surjective (σ) : Function.Surjective (orderedColumnRep Q Λ hQ L M f β h σ) := by
  rintro ⟨_, ⟨⟨_,y,rfl⟩,rfl⟩⟩; exact ⟨y,rfl⟩

theorem orderedColumnRep_val (σ) (y : V) :
    (orderedColumnRep Q Λ hQ L M f β h σ y).1.1 = q (F (orderedIdem Q Λ σ Bs) * (y*p)) := by
  change (act (orderedInclusion Q Λ hQ σ Bs 1) (columnRep Q Λ L M f β h y)).1 = _
  rw [orderedInclusion_one, blockProductAction_projection]
  change q (F (orderedIdem Q Λ σ Bs)) * q (F 1 * (y*p)) = _
  rw [← map_mul, ← mul_assoc, ← map_mul, mul_one]

/-- Cut a juxtaposed upper representative and a global lower representative, imposing the
local violations above and the higher bottom-order relations below the seam. -/
def crossingCut : diagrams Q Λ Bs ⊗[k] V →ₗ[k] Z :=
  ((BalancedTensor.mk k D₁ D₀ (BlockCut.space C) S₀).restrictScalars k) ∘ₗ
    TensorProduct.map ((C).cut ∘ₗ (π).toLinearMap) rep₀

local notation "splitAt" => crossingCut Q Λ hQ L M f β h

theorem crossingCut_tmul (x : diagrams Q Λ Bs) (y : V) :
    splitAt (x ⊗ₜ y) = BalancedTensor.tmul ((C).cut (π x)) (rep₀ y) := rfl

/-- Every balanced class is a sum of cuts of separated representatives. -/
theorem crossingCut_surjective : Function.Surjective splitAt := by
  have hx : Function.Surjective ((C).cut ∘ₗ (π).toLinearMap) :=
    (show Function.Surjective (C).cut from fun z => ⟨(C).incl z,(C).cut_incl z⟩).comp
      (projection_surjective Q Λ Bs)
  exact BalancedTensor.mk_surjective.comp (TensorProduct.map_surjective hx
    (orderedColumnRep_surjective Q Λ hQ L M f β h botOrd))

/-- **Stack after cutting a marked seam** (Webster, proof of Lemma 6.8). The result is
an exchanged-top representative of `F(x) F(e₀) y`, not the identity on unmarked diagrams. -/
theorem crossingStack_cut (x : diagrams Q Λ Bs) (y : V) :
    stk (splitAt (x ⊗ₜ y)) = rep₁ (F x * F E₀ * y) := by
  apply Subtype.ext; apply Subtype.ext
  rw [crossingCut_tmul, crossingStack_tmul, (C).incl_cut, orderedInclusion_one, orderedInclusion_one,
    ← map_mul, ← map_mul, blockProductAction_projection, orderedColumnRep_val, orderedColumnRep_val]
  rw [← map_mul, map_mul F, map_mul F]
  simp only [mul_assoc]
  have he : F E₀ * F E₀ = F E₀ := by
    -- The local order projector is idempotent already before taking violations.
    have idem : ∀ Bs', IsIdempotentElem (orderedIdem Q Λ botOrd Bs') := by
      intro Bs'; induction Bs' with
      | nil => exact one_mul (1 : diagrams Q Λ [])
      | cons B Bs' ih =>
        change (_ ⊗ₜ[k] _) * (_ ⊗ₜ[k] _) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, (isIdempotentElem_redProj _).eq, ih.eq]; rfl
    exact (map_mul F _ _).symm.trans (congrArg F (idem Bs).eq)
  rw [← mul_assoc (F E₀) (F E₀), he]

/-- Sliding an arbitrary diagram of the middle ordered algebra across the marked cut is
exactly the balancing relation, for any lift to local diagrams. -/
theorem crossingCut_slide (x a : diagrams Q Λ Bs) (d : D₀) (ha : π a = ι₀ d) (y : V) :
    splitAt ((x*a) ⊗ₜ y) = splitAt (x ⊗ₜ (F a*y)) := by
  have hx : (C).cut (π (x*a)) = op d • (C).cut (π x) := by
    apply (C).incl_injective
    rw [crossing_incl_right, (C).incl_cut, (C).incl_cut, map_mul, ha, unop_op]
    simp only [mul_assoc, ← map_mul, one_mul, mul_one]
  have hy : d • (rep₀ y) = rep₀ (F a*y) := by
    apply Subtype.ext; apply Subtype.ext
    change (act (ι₀ d) (rep₀ y).1).1 = _
    rw [← ha, blockProductAction_projection, orderedColumnRep_val, orderedColumnRep_val]
    have hcomm : act (π (a*E₀)) = act (π (E₀*a)) := by
      rw [map_mul π, map_mul π, ← orderedInclusion_one Q Λ hQ botOrd, ha, ← map_mul, ← map_mul,
        mul_one, one_mul]
    have he := congrArg Subtype.val (LinearMap.congr_fun hcomm (columnRep Q Λ L M f β h y))
    rw [blockProductAction_projection, blockProductAction_projection] at he
    change q (F (a*E₀)) * q (F 1 * (y*p)) = q (F (E₀*a)) * q (F 1 * (y*p)) at he
    simp only [← map_mul, ← mul_assoc, mul_one] at he
    simpa only [map_mul, mul_assoc] using he
  change (BalancedTensor.tmul ((C).cut (π (x*a))) (rep₀ y) : Z) = BalancedTensor.tmul ((C).cut (π x)) (rep₀ (F a*y))
  exact (congrArg (fun m => (BalancedTensor.tmul m (rep₀ y) : Z)) hx).trans
    ((BalancedTensor.op_smul_tmul ((C).cut (π x)) d (rep₀ y)).trans (congrArg (BalancedTensor.tmul ((C).cut (π x))) hy))

/-- Stacking commutes with the right action of the entire global bottom-order corner. -/
theorem crossingStack_right (b : (bottomIdempotent Q Λ L M f (ν := ν)).Cornerᵐᵒᵖ) (t : Z) :
    stk (b • t) = b • stk t := by
  have eqMaps : (stk).comp (BalancedTensor.mapRight (BalancedTensor.rmul D₀ S₀ b)) =
      (BalancedTensor.rmul D₁ S₁ b).comp stk := BalancedTensor.extB fun x z =>
    Subtype.ext (blockProductAction_right Q Λ L M f β h ((C).incl x) b z.1)
  exact LinearMap.congr_fun eqMaps t

/-- Naturality of the ordinary map after tensoring on the left with a right module in the
exchanged order. No inverse or derived natural transformation is asserted. -/
theorem crossingStack_natural {X Y : Type*} [AddCommGroup X] [Module k X] [Module D₁ᵐᵒᵖ X]
    [SMulCommClass k D₁ᵐᵒᵖ X] [AddCommGroup Y] [Module k Y] [Module D₁ᵐᵒᵖ Y]
    [SMulCommClass k D₁ᵐᵒᵖ Y] (g : X →ₗ[k] Y) (hg : ∀ (a : D₁) x, g (op a • x) = op a • g x) :
    (BalancedTensor.mapLeftOp k S₁ g hg) ∘ₗ (BalancedTensor.mapRight (k := k) (B := k) stk) =
      (BalancedTensor.mapRight (k := k) (B := k) stk) ∘ₗ (BalancedTensor.mapLeftOp k Z g hg) :=
  BalancedTensor.ext fun _ _ => rfl

end Categorification.Stendhal.RedBlock
