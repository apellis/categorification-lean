/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.CoverFurlingFibres
import Categorification.KLR.Unfurling.GenericWeights
import Categorification.KLR.Unfurling.FurlingVacuum

/-!
# The vacuum for the concrete generic cover

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
proof of the theorem labelled `nondegenerate`, construction of representations.
This assembles the constructed generic fields, independent labels, prescribed
cover weights and zero-block vacuum. The original colour type is arbitrary:
only finite weight support in each colour is needed. Neither a furling datum,
a base-pairing identity, a vacuum, nor any property of its endomorphisms is
assumed. `genericVacuumEv` and `genericVacuumBlockEv` are injective algebra maps
to the concrete field, and the vacuum vanishes away from `genericZeroBlock`.

The polynomial nonvanishing, weighted homogeneity and invertible symmetrizer
hypotheses remain explicit inputs. Specializing them to KL polynomials, and
constructing the complete furled 2-action, are separate steps. The vanishing
adapters from `FurlingVacuum` apply to this datum and object directly.
-/

noncomputable section
namespace Categorification.KLR.Unfurling.GenericFields
open CategoryTheory CategoryTheory.Limits Categorification.TwoRep
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

/-- The actual generic cover furling, for arbitrary colour types. -/
def genericFurling : Furling (coverProdWeight D) RD :=
  coverFurlingOfFibreFinite D Λm Λp RD μ
    (coverWeight_fibre_finite (zm k I Q) (zp k I Q)
      (negLevel s b M h) (posLevel s b M h) P₀ d hdpos hd hP hhom)

/-- Its spectral weight difference is exactly the prescribed original weight. -/
theorem generic_base_pair (i : I) :
    RD.pair (RD.iY i) μ = ∑ᶠ a : {a // (D).π a = i}, coverBaseVal Λm Λp a.1 :=
  (vacuum_finsum_base k s b M h P₀ d hdpos hd hP hhom i).symm

local notation "Φ" => genericFurling k RD μ s b M P₀ d hdpos hd hP hhom

/-- The constructed vacuum in the generic furling category. -/
def genericVacuum :
    (Φ).obj (coverProduct.{max u v, max u v, 0}
      (arrowsNeg D) (L := L₀) Λm (arrowsPos D) Λp) μ :=
  furledVacuum (arrowsNeg D) (L := L₀) Λm (arrowsPos D) Λp Φ
    (coverBase_eq_vacuumBase Λm Λp)

/-- Scalar evaluation on endomorphisms of the constructed generic vacuum. -/
def genericVacuumEv :
    End (genericVacuum k RD μ s b M P₀ d hdpos hd hP hhom) →ₐ[L₀] L₀ :=
  furledVacuumEv (arrowsNeg D) (L := L₀) Λm (arrowsPos D) Λp Φ
    (coverBase_eq_vacuumBase Λm Λp)

theorem genericVacuumEv_injective :
    Function.Injective (genericVacuumEv k RD μ s b M P₀ d hdpos hd hP hhom) :=
  furledVacuumEv_injective (arrowsNeg D) (L := L₀) Λm (arrowsPos D) Λp Φ
    (coverBase_eq_vacuumBase Λm Λp)

instance genericVacuum_isReduced :
    IsReduced (End (genericVacuum k RD μ s b M P₀ d hdpos hd hP hhom)) :=
  furledVacuum_isReduced (arrowsNeg D) (L := L₀) Λm (arrowsPos D) Λp Φ
    (coverBase_eq_vacuumBase Λm Λp)

/-- The zero block of the constructed generic furling. -/
def genericZeroBlock : (Φ).Blk μ := vacuumZeroBlock (arrowsNeg D) (arrowsPos D) Φ

/-- The scalar evaluation at the distinguished zero block. -/
def genericVacuumBlockEv :
    End (genericVacuum k RD μ s b M P₀ d hdpos hd hP hhom
      (genericZeroBlock k RD μ s b M P₀ d hdpos hd hP hhom)) →ₐ[L₀] L₀ :=
  furledVacuumBlockEv (arrowsNeg D) (L := L₀) Λm (arrowsPos D) Λp Φ
    (coverBase_eq_vacuumBase Λm Λp)

theorem genericVacuumBlockEv_injective :
    Function.Injective (genericVacuumBlockEv k RD μ s b M P₀ d hdpos hd hP hhom) :=
  furledVacuumBlockEv_injective (arrowsNeg D) (L := L₀) Λm (arrowsPos D) Λp Φ
    (coverBase_eq_vacuumBase Λm Λp)

instance genericVacuumBlock_isReduced :
    IsReduced (End (genericVacuum k RD μ s b M P₀ d hdpos hd hP hhom
      (genericZeroBlock k RD μ s b M P₀ d hdpos hd hP hhom))) :=
  isReduced_of_injective (genericVacuumBlockEv k RD μ s b M P₀ d hdpos hd hP hhom)
    (genericVacuumBlockEv_injective k RD μ s b M P₀ d hdpos hd hP hhom)

/-- The constructed vacuum vanishes at every other block. -/
theorem genericVacuum_isZero (β : (Φ).Blk μ)
    (hβ : β ≠ genericZeroBlock k RD μ s b M P₀ d hdpos hd hP hhom) :
    IsZero (genericVacuum k RD μ s b M P₀ d hdpos hd hP hhom β) :=
  furledVacuum_isZero (arrowsNeg D) (L := L₀) Λm (arrowsPos D) Λp Φ
    (coverBase_eq_vacuumBase Λm Λp) β hβ

end Categorification.KLR.Unfurling.GenericFields
