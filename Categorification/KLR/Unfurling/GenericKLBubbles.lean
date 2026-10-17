/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.GenericVacuumBubbles
import Categorification.KLR.Unfurling.GenericKLFamily
import Categorification.TwoRep.RouqUpBubbles

/-!
# Polynomial bubbles on the generic KL vacuum

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
proof of the theorem labelled `nondegenerate`, “Construction of representations”
and “Triviality of a relation”. This defines the polynomial bubble map by
categorical evaluation on the constructed generic vacuum. Injectivity of its
endomorphism evaluation identifies each bubble action with its scalar value.

The positive symmetrizer and its nonzero image in the ground field remain
intermediate hypotheses of the power-series construction, not restrictions
on the source nondegeneracy theorem.
-/

noncomputable section
namespace Categorification.KLR.Unfurling.GenericFields
open QuantumGroup QuantumGroup.UDot TwoRep MvPolynomial CategoryTheory CategoryTheory.Bicategory
universe u v w
variable {I : Type u} [DecidableEq I] (k : Type v) [Field k]
  {C : CartanDatum I} {X Y : Type w} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (μ : X) (s b M : ℕ)
  (d : I → ℕ) (hdpos : ∀ i, 0 < d i)
  (hd : ∀ i, (d i : k) ≠ 0)
  (hsym : ∀ i j, C.dot i j ≠ 0 → (d i : ℤ) * C.dot j j = d j * C.dot i i)

local notation "K₀" => K k (I × Slots s b)
local notation "L₀" => L k (I × Slots s b) (I × Slots s b)
local notation "P₀" => klP2 (k := K₀) C KL1.stdOrient

local notation "hdL" => kl_d_ne_zero k s b d hd
local notation "hP" => kl_map_ne_zero k (C := C) s b
local notation "hhom" => kl_map_homogeneous k s b d hsym
local notation "hPQ" => kl_factorization k (C := C) s b
local notation "hext" => kl_extremal k (C := C) s b
local notation "D" => coverDatum P₀ d hdpos hdL hP hhom
local notation "Λm" => vacuumWeightNeg k s b M (fun i => RD.pair (RD.iY i) μ)
local notation "Λp" => vacuumWeightPos k s b M (fun i => RD.pair (RD.iY i) μ)


local notation "T" => klRouqFamily k RD μ s b M d hdpos hd hsym
local notation "H" => klRouqFamily_brundanUpKLR k RD μ s b M d hdpos hd hsym
local notation "MI" => klRouqFamily_mixedInversion k RD μ s b M d hdpos hd hsym
local notation "h" => fun i => RD.pair (RD.iY i) μ
local notation "ev" => genericVacuumScalar k RD μ s b M P₀ d hdpos hdL hP hhom

attribute [local irreducible] coverProduct furledVacuum vacuumZeroBlock

attribute [local instance] ScalarRestriction.linearCatHom
  ScalarRestriction.precompLinear ScalarRestriction.postcompLinear

/-- Evaluation of identity-cell endomorphisms at the generic KL vacuum. -/
def klVacuumScalar : End (𝟙 ((T).obj μ)) →ₐ[L₀] L₀ := ev

local notation "ek" => klVacuumScalar k RD μ s b M d hdpos hd hsym

/-- Polynomial bubbles evaluated through the generic KL categorical action. -/
def klVacuumBubbleMap : KL3.Diagram.PiLam I k →ₐ[k] L₀ := by
  let e : End (𝟙 ((T).obj μ)) →ₐ[L₀] L₀ := ek
  letI : IsScalarTower k L₀ (End (𝟙 ((T).obj μ))) :=
    ScalarRestriction.tower k L₀ (𝟙 ((T).obj μ)) (𝟙 ((T).obj μ))
  exact (e.restrictScalars k).comp ((T).bubbleMap H MI μ)

/-- This scalar map is the component of `RouqFamily.bubbleMap` at the vacuum. -/
theorem klVacuumBubbleMap_apply (p : KL3.Diagram.PiLam I k) :
    klVacuumBubbleMap k RD μ s b M d hdpos hd hsym p =
      genericVacuumEv k RD μ s b M P₀ d hdpos hdL hP hhom
        (((T).bubbleMap H MI μ p).hom.app (klVacuum k RD μ s b M d hdpos hd hsym)) := rfl

private theorem scalar_of_injective {F A : Type*} [Field F] [Ring A] [Algebra F A]
    (e : A →ₐ[F] F) (he : Function.Injective e) (a : A) : a = e a • 1 := by
  apply he
  simp

/-- Vacuum bubble endomorphisms are scalar, by the injective vacuum evaluation. -/
theorem klVacuumBubbleMap_action (p : KL3.Diagram.PiLam I k) :
    (((T).bubbleMap H MI μ p).hom.app
      (klVacuum k RD μ s b M d hdpos hd hsym)) =
        klVacuumBubbleMap k RD μ s b M d hdpos hd hsym p • 𝟙 _ := by
  exact scalar_of_injective (genericVacuumEv k RD μ s b M P₀ d hdpos hdL hP hhom)
    (genericVacuumEv_injective k RD μ s b M P₀ d hdpos hdL hP hhom) _

end Categorification.KLR.Unfurling.GenericFields
