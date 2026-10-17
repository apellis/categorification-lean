/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.GenericVacuumBubbles
import Categorification.KLR.Unfurling.GenericKLFamily
import Categorification.TwoRep.RouqUpBubbles
import Categorification.KLR.Unfurling.CoverBubbleCompatibility

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

/-- The scalar bubble evaluation is injective on polynomials in the bounded variables. -/
theorem vacuumBubbleEval_rename_injective (k : Type v) [Field k] {I : Type u}
    (s b M : ℕ) (h : I → ℤ) {N : ℕ} (hN : N ≤ b) :
    Function.Injective (fun p : MvPolynomial {p : I × ℕ // p.2 < N} k =>
      vacuumBubbleEval k s b M h (MvPolynomial.rename Subtype.val p)) := by
  have he : (vacuumBubbleEval k s b M h).comp
      (MvPolynomial.rename (fun p : {p : I × ℕ // p.2 < N} => p.val)) =
      MvPolynomial.aeval (fun p : {p : I × ℕ // p.2 < N} =>
        vacuumBubbleEval k s b M h (MvPolynomial.X p.val)) := by
    ext p
    simp
  change Function.Injective ((vacuumBubbleEval k s b M h).comp
    (MvPolynomial.rename (fun p : {p : I × ℕ // p.2 < N} => p.val)))
  rw [he]
  exact vacuumBubbleEval_indep k s b M h hN

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
local notation "Φ" => genericFurling k RD μ s b M P₀ d hdpos hdL hP hhom
local notation "ev" => genericVacuumScalar k RD μ s b M P₀ d hdpos hdL hP hhom

attribute [local irreducible] coverProduct furledVacuum vacuumZeroBlock

attribute [local instance] ScalarRestriction.linearCatHom
  ScalarRestriction.precompLinear ScalarRestriction.postcompLinear

/-- Evaluation of identity-cell endomorphisms at the generic KL vacuum. -/
def klVacuumScalar : End (𝟙 ((T).obj μ)) →ₐ[L₀] L₀ := ev

local notation "ek" => klVacuumScalar k RD μ s b M d hdpos hd hsym

/-- The assembled KL family has the explicit generic furling generators. -/
theorem kl_localData_eq (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z) :
    (T).localData i h₁ h₂ = (Φ).localData (coverProduct.{max u v,max u v,0} (arrowsNeg D) (L := L₀) Λm (arrowsPos D) Λp) D i h₁ h₂ := by
  exact coverRouqFamily_localData_eq D Λm Λp RD μ
    (coverWeightNeg_finite_fibre (zm k I (Slots s b)) (negLevel s b M h))
    (coverWeightPos_finite_fibre (zp k I (Slots s b)) (posLevel s b M h))
    (coverDatum_noCrossArrows P₀ d hdpos hdL hP hhom)
    (generic_base_pair k RD μ s b M P₀ d hdpos hdL hP hhom)
    (coverDatum_finsum_arrows P₀ d hdpos hdL hP hhom C RD
      (klQ2 L₀ C) (kl_factorization k (C := C) s b) (kl_extremal k (C := C) s b))
    (kl_factorization k (C := C) s b)
    (coverWeight_fibre_finite (zm k I (Slots s b)) (zp k I (Slots s b))
      (negLevel s b M h) (posLevel s b M h) P₀ d hdpos hdL hP hhom) i h₁ h₂


/-- At nonnegative weight, the actual counterclockwise bubble has its generic value. -/
theorem klVacuumScalar_ccw (hbpos : 0 < b) (i : I) (hh : 0 ≤ h i) (n : ℕ) :
    (ek) (((T).loc i (sub_add_cancel _ _) rfl).ccw (h i + n).toNat) =
      vacuumBubbleEval k s b M h (MvPolynomial.X (i,n)) := by
  exact (Φ).evalFamily_ccw (coverProduct.{max u v,max u v,0} (arrowsNeg D) (L := L₀) Λm (arrowsPos D) Λp) D T i (sub_add_cancel μ (RD.iX i)) rfl
    (kl_localData_eq k RD μ s b M d hdpos hd hsym i (sub_add_cancel μ (RD.iX i)) rfl)
    (ek) (ev) HEq.rfl ((h i + n).toNat : ℤ) _
    (fun loc => generic_ccw_value k RD μ s b M P₀ d hdpos hdL hP hhom hbpos i
      (sub_add_cancel μ (RD.iX i)) rfl loc hh n)

/-- At negative weight, the actual clockwise bubble has its generic value. -/
theorem klVacuumScalar_cw (hbpos : 0 < b) (i : I) (hh : h i < 0) (n : ℕ) :
    (ek) (((T).loc i (sub_add_cancel _ _) rfl).cw (-h i + n).toNat) =
      vacuumBubbleEval k s b M h (MvPolynomial.X (i,n)) := by
  refine (Φ).evalFamily_cw (coverProduct.{max u v,max u v,0} (arrowsNeg D) (L := L₀) Λm (arrowsPos D) Λp) D T i (sub_add_cancel μ (RD.iX i)) rfl
    (kl_localData_eq k RD μ s b M d hdpos hd hsym i (sub_add_cancel μ (RD.iX i)) rfl)
    (ek) (ev) HEq.rfl ((-h i + n).toNat : ℤ) _ ?_
  intro loc
  exact generic_cw_value k RD μ s b M P₀ d hdpos hdL hP hhom hbpos i
    (sub_add_cancel μ (RD.iX i)) rfl loc hh n


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

/-- Each polynomial generator evaluates to its generic scalar bubble coefficient. -/
theorem klVacuumBubbleMap_X (hbpos : 0 < b) (i : I) (n : ℕ) :
    klVacuumBubbleMap k RD μ s b M d hdpos hd hsym (MvPolynomial.X (i,n)) =
      vacuumBubbleEval k s b M h (MvPolynomial.X (i,n)) := by
  let e : End (𝟙 ((T).obj μ)) →ₐ[L₀] L₀ := ek
  change e ((T).bubbleMap H MI μ (MvPolynomial.X (i,n))) = _
  have hx := congrArg e
    ((T).bubbleMap_X H MI i (sub_add_cancel _ _) rfl n)
  refine hx.trans ?_
  change e (if 0 ≤ h i then _ else _) = _
  by_cases hh : 0 ≤ h i
  · rw [ite_eq_left hh]
    have hn : ((h i + n).toNat : ℤ) = h i - 1 + (n + 1 : ℕ) := by omega
    have hv := klVacuumScalar_ccw k RD μ s b M d hdpos hd hsym hbpos i hh n
    simpa only [hn, KL3.Diagram.ip] using hv
  · rw [ite_eq_right hh]
    have hh' : h i < 0 := lt_of_not_ge hh
    have hn : ((-h i + n).toNat : ℤ) = -h i - 1 + (n + 1 : ℕ) := by omega
    have hv := klVacuumScalar_cw k RD μ s b M d hdpos hd hsym hbpos i hh' n
    simpa only [hn, KL3.Diagram.ip] using hv

/-- The actual categorical polynomial bubble map is the generic scalar evaluation. -/
theorem klVacuumBubbleMap_eq (hbpos : 0 < b) :
    klVacuumBubbleMap k RD μ s b M d hdpos hd hsym = vacuumBubbleEval k s b M h := by
  ext p
  exact klVacuumBubbleMap_X k RD μ s b M d hdpos hd hsym hbpos p.1 p.2

/-- The actual bubble values in any slot bound are algebraically independent. -/
theorem klVacuumBubbleMap_independent (hbpos : 0 < b) {N : ℕ} (hN : N ≤ b) :
    AlgebraicIndependent k (fun p : {p : I × ℕ // p.2 < N} =>
      klVacuumBubbleMap k RD μ s b M d hdpos hd hsym (MvPolynomial.X p.1)) := by
  rw [klVacuumBubbleMap_eq k RD μ s b M d hdpos hd hsym hbpos]
  exact vacuumBubbleEval_indep k s b M h hN

/-- The categorical vacuum bubble action is the explicit generic scalar action. -/
theorem klVacuumBubbleMap_scalar (hbpos : 0 < b) (p : KL3.Diagram.PiLam I k) :
    (((T).bubbleMap H MI μ p).hom.app
      (klVacuum k RD μ s b M d hdpos hd hsym)) =
        vacuumBubbleEval k s b M h p • 𝟙 _ := by
  rw [klVacuumBubbleMap_action, klVacuumBubbleMap_eq k RD μ s b M d hdpos hd hsym hbpos]

end Categorification.KLR.Unfurling.GenericFields
