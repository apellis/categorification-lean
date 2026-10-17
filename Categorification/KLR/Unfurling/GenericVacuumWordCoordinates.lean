/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.GenericVacuumCoordinates

noncomputable section
open CategoryTheory Categorification.QuantumGroup Categorification.QuantumGroup.UDot
  Categorification.TwoRep
open Categorification.KLR Categorification.KLR.Unfurling
open Categorification.KLR.CyclotomicAction
namespace Categorification.KLR.Unfurling.GenericFields
universe u v w
variable (k : Type v) [Field k] {I : Type u}
variable {C : CartanDatum I} {X Y : Type w} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (μ : X) (s b M : ℕ)
  (P₀ : I → I → MvPolynomial (Fin 2) (K k (I × Slots s b)))
  (d : I → ℕ) (hdpos : ∀ i, 0 < d i)
  (hd : ∀ i, (d i : L k (I × Slots s b) (I × Slots s b)) ≠ 0)
  (hP : ∀ i j, i ≠ j → MvPolynomial.map
    (algebraMap (K k (I × Slots s b)) (L k (I × Slots s b) (I × Slots s b))) (P₀ i j) ≠ 0)
  (hhom : ∀ i j, i ≠ j → ∃ D, (MvPolynomial.map
    (algebraMap (K k (I × Slots s b)) (L k (I × Slots s b) (I × Slots s b)))
      (P₀ i j)).IsWeightedHomogeneous ![d j, d i] D)

local notation "L₀" => L k (I × Slots s b) (I × Slots s b)
local notation "D" => coverDatum P₀ d hdpos hd hP hhom
local notation "Λm" => vacuumWeightNeg k s b M (fun i => RD.pair (RD.iY i) μ)
local notation "Λp" => vacuumWeightPos k s b M (fun i => RD.pair (RD.iY i) μ)
local notation "nm" => arrowsNeg D
local notation "np" => arrowsPos D
local notation "Φ" => genericFurling k RD μ s b M P₀ d hdpos hd hP hhom
local notation "β₀" => genericZeroBlock k RD μ s b M P₀ d hdpos hd hP hhom


/-- The normalized coordinates of every upward word on the positive regular vacuum
evaluate its generator to the word idempotent. -/
theorem genericVacuum_wcoord_wgen (νm : Multiset (LabelNeg I (K k (I × Slots s b)) L₀)) (t : Seq νm) :
    wcoord (unfQ_klrSymm nm) (cover_hlead nm) (cover_hmonic Λm)
      (cover_hΛ nm Λm) (cover_hdeg nm)
      (genericVacuumModule k RD μ s b M P₀ d hdpos hd hP hhom)
      (by simp [blockWeight]) (genericVacuumModuleCoord k RD μ s b M P₀ d hdpos hd hP hhom) t
      (wgen (unfQ_klrSymm nm) (cover_hlead nm) (cover_hmonic Λm)
        (cover_hΛ nm Λm) (cover_hdeg nm)
        (genericVacuumModule k RD μ s b M P₀ d hdpos hd hP hhom)
        (by simp [blockWeight]) (genericVacuumModuleGen k RD μ s b M P₀ d hdpos hd hP hhom) t) =
      CycKLR.mk L₀ (unfQ nm) (fun a => Polynomial.X ^ Λm a) νm (KLRAlgebra.e t.rev) := by
  exact wcoord_wgen _ _ _ _ _ _ _ _
    (genericVacuumModuleCoord_gen k RD μ s b M P₀ d hdpos hd hP hhom) t

end Categorification.KLR.Unfurling.GenericFields
