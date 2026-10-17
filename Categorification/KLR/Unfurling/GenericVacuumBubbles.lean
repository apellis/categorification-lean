/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.GenericVacuumEdges
import Categorification.KLR.Unfurling.GenericBubbleValues

/-!
# Categorical bubbles evaluated at the generic vacuum

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
proof of `nondegenerate`, “Triviality of a relation”. The categorical vacuum
formulas, reindexed by finite slots, agree with the scalar bubble evaluation.
The hypothesis `0 < b` ensures a positive total degree for both orientations;
it is satisfied by choosing one more bubble slot than the required degree bound.
-/

noncomputable section
open CategoryTheory CategoryTheory.Bicategory
namespace Categorification.TwoRep.LinearCat
universe u v w
variable {L : Type u} [CommRing L]
/-- Evaluation of an identity-functor endomorphism at an object, as an algebra map. -/
def idEndEval (C : LinearCat.{u,v,w} L) (V : C) : End (𝟙 C) →ₐ[L] End V where
  toFun η := η.hom.app V
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
end Categorification.TwoRep.LinearCat

namespace Categorification.KLR.Unfurling.GenericFields
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits TwoRep TwoRep.Furling
universe u v w
variable (k : Type v) [Field k] {I : Type u} {C : QuantumGroup.CartanDatum I}
  {X Y : Type w} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.WeightDatum C X Y) (μ : X) (s b M : ℕ)

local notation "Q" => Slots s b
local notation "K₀" => K k (I × Q)
local notation "L₀" => L k (I × Q) (I × Q)
local notation "h" => fun i => RD.pair (RD.iY i) μ
local notation "Λm" => vacuumWeightNeg k s b M h
local notation "Λp" => vacuumWeightPos k s b M h

variable (P₀ : I → I → MvPolynomial (Fin 2) (K k (I × Slots s b))) (d : I → ℕ) (hdpos : ∀ i, 0 < d i)
  (hd : ∀ i, ((d i : ℕ) : (L k (I × Slots s b) (I × Slots s b))) ≠ 0)
  (hP : ∀ i j, i ≠ j → MvPolynomial.map (algebraMap (K k (I × Slots s b)) (L k (I × Slots s b) (I × Slots s b))) (P₀ i j) ≠ 0)
  (hhom : ∀ i j, i ≠ j → ∃ D,
    (MvPolynomial.map (algebraMap (K k (I × Slots s b)) (L k (I × Slots s b) (I × Slots s b))) (P₀ i j)).IsWeightedHomogeneous ![d j, d i] D)

local notation "D" => coverDatum P₀ d hdpos hd hP hhom

local notation "nm" => arrowsNeg D
local notation "np" => arrowsPos D
local notation "Φ" => genericFurling k RD μ s b M P₀ d hdpos hd hP hhom
local notation "V" => genericVacuum k RD μ s b M P₀ d hdpos hd hP hhom
local notation "β₀" => genericZeroBlock k RD μ s b M P₀ d hdpos hd hP hhom
local notation "hb" => coverBase_eq_vacuumBase Λm Λp
attribute [local irreducible] coverProduct furledVacuum vacuumZeroBlock


local notation "RDc" => coverProdWeight D

/-- Scalar evaluation of natural endomorphisms on the constructed generic vacuum. -/
def genericVacuumScalar : End (𝟙 ((Φ).obj (coverProduct.{max u v,max u v,0} nm (L := L₀) Λm np Λp) μ)) →ₐ[L₀] L₀ :=
  (genericVacuumEv k RD μ s b M P₀ d hdpos hd hP hhom).comp
    (LinearCat.idEndEval ((Φ).obj (coverProduct.{max u v,max u v,0} nm (L := L₀) Λm np Λp) μ) V)

theorem genericVacuumScalar_apply (η : End (𝟙 ((Φ).obj (coverProduct.{max u v,max u v,0} nm (L := L₀) Λm np Λp) μ))) :
    genericVacuumScalar k RD μ s b M P₀ d hdpos hd hP hhom η =
      genericVacuumBlockEv k RD μ s b M P₀ d hdpos hd hP hhom (η.hom.app V β₀) := rfl

/-- At negative weight, the local clockwise generator has the prescribed scalar value.
The local Rouquier structure is an input; the vacuum, its concentration and all
spectral products are constructed. The positive slot count is a route hypothesis. -/
theorem generic_cw_value (hbpos : 0 < b)
    (i : I) {l₀ l' : X} (h₀ : l₀ + RD.iX i = μ) (hi : μ + RD.iX i = l')
    {τ : E Φ (coverProduct.{max u v,max u v,0} nm (L := L₀) Λm np Λp) i h₀ ≫ E Φ (coverProduct.{max u v,max u v,0} nm (L := L₀) Λm np Λp) i hi ⟶ E Φ (coverProduct.{max u v,max u v,0} nm (L := L₀) Λm np Λp) i h₀ ≫ E Φ (coverProduct.{max u v,max u v,0} nm (L := L₀) Λm np Λp) i hi}
    (loc : RouqLoc ((Φ).adj (coverProduct.{max u v,max u v,0} nm (L := L₀) Λm np Λp) i h₀) ((Φ).adj (coverProduct.{max u v,max u v,0} nm (L := L₀) Λm np Λp) i hi)
      (dot Φ (coverProduct.{max u v,max u v,0} nm (L := L₀) Λm np Λp) (D).pw i h₀) (dot Φ (coverProduct.{max u v,max u v,0} nm (L := L₀) Λm np Λp) (D).pw i hi) τ (h i))
    (hh : h i < 0) (n : ℕ) :
    genericVacuumScalar k RD μ s b M P₀ d hdpos hd hP hhom
      (loc.cw (-h i + n).toNat) =
      vacuumBubbleEval k s b M h (MvPolynomial.X (i, n)) := by
  classical
  let : IsReduced (End (V β₀)) :=
    genericVacuumBlock_isReduced k RD μ s b M P₀ d hdpos hd hP hhom
  have hsum : ((∑ q, posLevel s b M h i q : ℕ) : ℤ) -
      (∑ q, negLevel s b M h i q : ℕ) = h i := by
    simpa only [Finset.sum_sub_distrib, Nat.cast_sum] using sum_level_difference s b M h i
  have hN : (∑ a : OutEdge Φ i β₀, (-(RDc).pair ((RDc).iY a.1.lbl) ((Φ).wtT β₀.1)).toNat) =
      (-h i).toNat + ∑ a : InEdge Φ i h₀ β₀, ((RDc).pair ((RDc).iY a.1.lbl) ((Φ).wtT β₀.1)).toNat := by
    rw [vacuum_sum_out, vacuum_sum_in]
    omega
  have hNpos : 0 < ∑ a : OutEdge Φ i β₀,
      (-(RDc).pair ((RDc).iY a.1.lbl) ((Φ).wtT β₀.1)).toNat := by
    rw [vacuum_sum_out]
    simp only [Fintype.sum_sum_type, negLevel, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]
    omega
  have hv := cw_app_vacuum Φ (coverProduct.{max u v,max u v,0} nm (L := L₀) Λm np Λp) (D).pw i h₀ hi V β₀ loc hh.le
    (genericVacuum_isZero k RD μ s b M P₀ d hdpos hd hP hhom)
    (fun c _ _ hc => coverProduct_dot_nilpotent nm (L := L₀) Λm np Λp c hc)
    (furledVacuum_out nm (L := L₀) Λm np Λp Φ hb i hi)
    (furledVacuum_posIn nm (L := L₀) Λm np Λp Φ hb i h₀)
    (fun a ha a' ha' he => (D).pw_coeff_zero_inj a a' (ha.trans ha'.symm) he)
    (fun p => (D).pw_coeff_one p.1.1.lbl) hN hNpos
    (genericVacuumBlockEv k RD μ s b M P₀ d hdpos hd hP hhom) (-h i + n).toNat
  conv_rhs => rw [vacuumBubbleEval, bubbleEval_X_of_neg k h _ _ i hh]
  simp only [zpow_neg, zpow_natCast, ← inv_pow] at hv ⊢
  conv at hv =>
    rhs
    rw [vacuum_prod_in k RD μ s b M P₀ d hdpos hd hP hhom i h₀
      (fun a => 1 - PowerSeries.C (((D).pw a).coeff 0) * PowerSeries.X),
      vacuum_prod_out k RD μ s b M P₀ d hdpos hd hP hhom i
        (fun a => (oneSubUnit (((D).pw a).coeff 0))⁻¹)]
  rw [genericVacuumScalar_apply]
  simpa only [coverDatum_pw_coeff_zero, coverLabel, zm, zp, neg, pos,
    Algebra.algebraMap_self_apply] using hv

/-- At nonnegative weight, the local counterclockwise generator has the prescribed
scalar value, under the same local-structure and positive-slot hypotheses as
`generic_cw_value`. The categorical and scalar conventions retain their dot shift. -/
theorem generic_ccw_value (hbpos : 0 < b)
    (i : I) {l₀ l' : X} (h₀ : l₀ + RD.iX i = μ) (hi : μ + RD.iX i = l')
    {τ : E Φ (coverProduct.{max u v,max u v,0} nm (L := L₀) Λm np Λp) i h₀ ≫ E Φ (coverProduct.{max u v,max u v,0} nm (L := L₀) Λm np Λp) i hi ⟶ E Φ (coverProduct.{max u v,max u v,0} nm (L := L₀) Λm np Λp) i h₀ ≫ E Φ (coverProduct.{max u v,max u v,0} nm (L := L₀) Λm np Λp) i hi}
    (loc : RouqLoc ((Φ).adj (coverProduct.{max u v,max u v,0} nm (L := L₀) Λm np Λp) i h₀) ((Φ).adj (coverProduct.{max u v,max u v,0} nm (L := L₀) Λm np Λp) i hi)
      (dot Φ (coverProduct.{max u v,max u v,0} nm (L := L₀) Λm np Λp) (D).pw i h₀) (dot Φ (coverProduct.{max u v,max u v,0} nm (L := L₀) Λm np Λp) (D).pw i hi) τ (h i))
    (hh : 0 ≤ h i) (n : ℕ) :
    genericVacuumScalar k RD μ s b M P₀ d hdpos hd hP hhom
      (loc.ccw (h i + n).toNat) =
      vacuumBubbleEval k s b M h (MvPolynomial.X (i, n)) := by
  classical
  let : IsReduced (End (V β₀)) :=
    genericVacuumBlock_isReduced k RD μ s b M P₀ d hdpos hd hP hhom
  have hsum : ((∑ q, posLevel s b M h i q : ℕ) : ℤ) -
      (∑ q, negLevel s b M h i q : ℕ) = h i := by
    simpa only [Finset.sum_sub_distrib, Nat.cast_sum] using sum_level_difference s b M h i
  have hN : (∑ a : InEdge Φ i h₀ β₀, ((RDc).pair ((RDc).iY a.1.lbl) ((Φ).wtT β₀.1)).toNat) =
      (h i).toNat + ∑ a : OutEdge Φ i β₀, (-(RDc).pair ((RDc).iY a.1.lbl) ((Φ).wtT β₀.1)).toNat := by
    rw [vacuum_sum_out, vacuum_sum_in]
    omega
  have hNpos : 0 < ∑ a : InEdge Φ i h₀ β₀,
      ((RDc).pair ((RDc).iY a.1.lbl) ((Φ).wtT β₀.1)).toNat := by
    rw [vacuum_sum_in]
    simp only [Fintype.sum_sum_type, posLevel, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]
    omega
  have hv := ccw_app_vacuum Φ (coverProduct.{max u v,max u v,0} nm (L := L₀) Λm np Λp) (D).pw i h₀ hi V β₀ loc hh
    (genericVacuum_isZero k RD μ s b M P₀ d hdpos hd hP hhom)
    (fun c _ _ hc => coverProduct_dot_nilpotent nm (L := L₀) Λm np Λp c hc)
    (furledVacuum_in nm (L := L₀) Λm np Λp Φ hb i h₀)
    (furledVacuum_negOut nm (L := L₀) Λm np Λp Φ hb i)
    (fun a ha a' ha' he => (D).pw_coeff_zero_inj a a' (ha.trans ha'.symm) he)
    (fun p => (D).pw_coeff_one p.1.1.lbl) hN hNpos
    (genericVacuumBlockEv k RD μ s b M P₀ d hdpos hd hP hhom) (h i + n).toNat
  conv_rhs => rw [vacuumBubbleEval, bubbleEval_X_of_nonneg k h _ _ i hh]
  simp only [zpow_neg, zpow_natCast, ← inv_pow] at hv ⊢
  conv at hv =>
    rhs
    rw [vacuum_prod_out k RD μ s b M P₀ d hdpos hd hP hhom i
      (fun a => 1 - PowerSeries.C (((D).pw a).coeff 0) * PowerSeries.X),
      vacuum_prod_in k RD μ s b M P₀ d hdpos hd hP hhom i h₀
        (fun a => (oneSubUnit (((D).pw a).coeff 0))⁻¹)]
  rw [genericVacuumScalar_apply]
  simpa only [coverDatum_pw_coeff_zero, coverLabel, zm, zp, neg, pos,
    Algebra.algebraMap_self_apply] using hv

end Categorification.KLR.Unfurling.GenericFields
