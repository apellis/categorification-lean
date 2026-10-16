/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.CoverMixedInversion
import Categorification.KLR.Unfurling.GenericVacuum
import Categorification.TwoRep.FurlingKL

/-!
# The generic KL action and its vacuum evaluation

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
§2.3, Lemma `lem:g-action`, supporting the theorem labelled `nondegenerate`.
The crossing factors are `klP2 C KL1.stdOrient` over the constructed field `K`.
All polynomial inputs of the spectral cover are proved, including the extremal
coefficient. The resulting family has Brundan's upward and mixed inversion
relations and evaluates the unchanged k-presentation at `genericVacuum`.

The remaining hypotheses are a positive natural symmetrizer `d`, compatibility
`C.dot i j ≠ 0 → (d i : ℤ) * C.dot j j = d j * C.dot i i`, and
`(d i : k) ≠ 0` for every colour. No compatibility or characteristic condition
is weakened here. The last condition is needed by this power-series route, not
by the final nondegeneracy statement. No `UnfurledEval` or nondegeneracy theorem
is asserted in this module.
-/

noncomputable section
namespace Categorification.KLR.Unfurling.GenericFields
open QuantumGroup QuantumGroup.UDot TwoRep MvPolynomial CategoryTheory
open KLR.Diagram KL3.Diagram
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

omit [DecidableEq I] in
include hd in
/-- Nonzero symmetrizer coefficients remain nonzero in the constructed field. -/
theorem kl_d_ne_zero (i : I) : (d i : L₀) ≠ 0 := by
  simpa only [map_natCast] using ((map_ne_zero (algebraMap k L₀)).2 (hd i))

omit [DecidableEq I] in
/-- The standard KL crossing factors remain nonzero after coefficient extension. -/
theorem kl_map_ne_zero (i j : I) (hij : i ≠ j) :
    MvPolynomial.map (algebraMap K₀ L₀) (P₀ i j) ≠ 0 := by
  rw [map_klP2]
  exact klP2_ne_zero i j hij

omit [DecidableEq I] in
include hsym in
/-- The chosen positive symmetrizer supplies the required reversed variable weights. -/
theorem kl_map_homogeneous (i j : I) (hij : i ≠ j) :
    ∃ D, (MvPolynomial.map (algebraMap K₀ L₀) (P₀ i j)).IsWeightedHomogeneous
      ![d j, d i] D := by
  rw [map_klP2]
  exact klP2_isWeightedHomogeneous C KL1.stdOrient d hsym i j hij

omit [DecidableEq I] in
/-- Factorization of the KL polynomials over the generic coefficient field. -/
theorem kl_factorization (i j : I) (hij : i ≠ j) :
    klQ2 L₀ C i j = MvPolynomial.map (algebraMap K₀ L₀) (P₀ j i) *
      rename ![1, 0] (MvPolynomial.map (algebraMap K₀ L₀) (P₀ i j)) := by
  simp only [map_klP2]
  exact klQ2_eq_klP2 KL2.stdOrient_spec i j hij

omit [DecidableEq I] in
/-- The extremal coefficient is a unit (in fact, one) in every characteristic. -/
theorem kl_extremal (i j : I) (hij : i ≠ j) :
    (klQ2 L₀ C i j).coeff (Finsupp.single 0 (C.dij i j)) ≠ 0 := by
  rw [klQ2_coeff_extremal C i j hij]
  exact one_ne_zero

local notation "hdL" => kl_d_ne_zero k s b d hd
local notation "hP" => kl_map_ne_zero k (C := C) s b
local notation "hhom" => kl_map_homogeneous k s b d hsym
local notation "hPQ" => kl_factorization k (C := C) s b
local notation "hext" => kl_extremal k (C := C) s b
local notation "D" => coverDatum P₀ d hdpos hdL hP hhom
local notation "Λm" => vacuumWeightNeg k s b M (fun i => RD.pair (RD.iY i) μ)
local notation "Λp" => vacuumWeightPos k s b M (fun i => RD.pair (RD.iY i) μ)

/-- The generic KL Rouquier family, with no polynomial hypotheses. -/
def klRouqFamily :=
  rouqFamily.{u, v, 0, w} k s b M RD μ P₀ d hdpos hdL hP hhom
    (klQ2 L₀ C) hPQ hext

local notation "T" => klRouqFamily k RD μ s b M d hdpos hd hsym

/-- The constructed generic vacuum is an object of the KL family at its base weight. -/
def klVacuum : (T).obj μ :=
  genericVacuum k RD μ s b M P₀ d hdpos hdL hP hhom

/-- Upward KL relations for the generic family, with all cover inputs supplied. -/
theorem klRouqFamily_upKLR : RouqUpKLR T (klQ2 L₀ C) :=
  coverRouqFamily_upKLR D Λm Λp RD μ
    (coverWeightNeg_finite_fibre (zm k I (Slots s b)) _)
    (coverWeightPos_finite_fibre (zp k I (Slots s b)) _)
    (coverDatum_noCrossArrows P₀ d hdpos hdL hP hhom)
    (generic_base_pair k RD μ s b M P₀ d hdpos hdL hP hhom)
    (coverDatum_finsum_arrows P₀ d hdpos hdL hP hhom C RD (klQ2 L₀ C) hPQ hext) hPQ

attribute [local instance] ScalarRestriction.linearCatHom
  ScalarRestriction.precompLinear ScalarRestriction.postcompLinear

/-- Brundan's upward relations for the original ground-field KL scalars. -/
theorem klRouqFamily_brundanUpKLR :
    BrundanUpKLR T (CL.CLScalars.kl : CL.CLScalars C k) :=
  (klRouqFamily_upKLR k RD μ s b M d hdpos hd hsym).brundan_kl_restrictScalars

/-- Brundan's mixed inversion for the generic KL family. -/
theorem klRouqFamily_mixedInversion : BrundanMixedInversion T :=
  rouqFamily_mixedInversion k s b M RD μ P₀ d hdpos hdL hP hhom
    (klQ2 L₀ C) hPQ hext

/-- Semilinear evaluation of the k-presentation at the constructed generic vacuum.
Neither an action relation nor a vacuum object is an input. -/
def klVacuumUpEval {ν : Multiset I} {t t' : Seq ν} :
    ((pres RD k).obj (ob RD μ (ups (word t))) ⟶
      (pres RD k).obj (ob RD μ (ups (word t')))) →ₛₗ[algebraMap k L₀]
      (((T).wordCell μ t).obj.obj (klVacuum k RD μ s b M d hdpos hd hsym) ⟶
        ((T).wordCell μ t').obj.obj (klVacuum k RD μ s b M d hdpos hd hsym)) :=
  (T).upEvalAtSemilinear (klRouqFamily_upKLR k RD μ s b M d hdpos hd hsym)
    (klRouqFamily_mixedInversion k RD μ s b M d hdpos hd hsym) μ
    (klVacuum k RD μ s b M d hdpos hd hsym)

/-- The evaluation is the component of the KL action at the generic vacuum. -/
@[simp] theorem klVacuumUpEval_apply {ν : Multiset I} {t t' : Seq ν}
    (f : (pres RD k).obj (ob RD μ (ups (word t))) ⟶
      (pres RD k).obj (ob RD μ (ups (word t')))) :
    klVacuumUpEval k RD μ s b M d hdpos hd hsym f =
      ((T).upEval (klRouqFamily_brundanUpKLR k RD μ s b M d hdpos hd hsym)
        (klRouqFamily_mixedInversion k RD μ s b M d hdpos hd hsym) μ f).hom.app
        (klVacuum k RD μ s b M d hdpos hd hsym) := rfl

end Categorification.KLR.Unfurling.GenericFields
