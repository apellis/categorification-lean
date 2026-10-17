/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.GenericKLFamily
import Categorification.KLR.Unfurling.GenericStrands
import Categorification.KLR.Unfurling.VacuumEvaluation
import Categorification.KLR.Unfurling.GenericBubbleValues

/-!
# Concrete generic evaluation interfaces

Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
proof of the theorem labelled `nondegenerate`, “Triviality of a relation”.

The generic KL action has the concrete block data used by the vacuum, and its
crossing factors descend to the ground field. Equality transports identify the
projected strand sequence with the original sequence. The positive diagonal
lengths provide the power-series symmetrizer in characteristic zero.

These interfaces support the concrete assembly; they do not yet assert
nondegeneracy or assume a basis-image formula.
-/

noncomputable section
namespace Categorification.KLR.Unfurling
open QuantumGroup QuantumGroup.UDot TwoRep CategoryTheory
universe u v w
variable {I : Type u} [DecidableEq I] {C : CartanDatum I}
  {X Y : Type w} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type v} [Field k]

/-- Reindex an evaluation along equality of its original colour weight. -/
def UnfurledEval.reindex {μ : X} {ν ν' : Multiset I} (hν : ν' = ν)
    {t : Seq ν'} {i j : Seq ν} (ht : hν ▸ t = i) {N : ℕ}
    (E : UnfurledEval RD k μ t (hν.symm ▸ j) N) :
    UnfurledEval RD k μ i j N := by
  subst ν
  subst i
  exact E

omit [DecidableEq I] in
/-- Reindexing a projected sequence agrees with its projection to the identified weight. -/
theorem cast_down {J : Type*} (π : J → I) {ν' : Multiset J} {ν : Multiset I}
    (hν : ν'.map π = ν) (t : Seq ν') :
    hν ▸ down π rfl t = down π hν t := by
  subst ν
  rfl

namespace GenericFields
variable (k RD) (μ : X) (s b M : ℕ)
  (d : I → ℕ) (hdpos : ∀ i, 0 < d i) (hd : ∀ i, (d i : k) ≠ 0)
  (hsym : ∀ i j, C.dot i j ≠ 0 → (d i : ℤ) * C.dot j j = d j * C.dot i i)
local notation "K₀" => K k (I × Slots s b)
local notation "L₀" => L k (I × Slots s b) (I × Slots s b)
local notation "P₀" => klP2 (k := K₀) C KL1.stdOrient
local notation "hdL" => kl_d_ne_zero k s b d hd
local notation "hP" => kl_map_ne_zero k (C := C) s b
local notation "hhom" => kl_map_homogeneous k s b d hsym
local notation "D" => coverDatum P₀ d hdpos hdL hP hhom
local notation "Φ" => genericFurling k RD μ s b M P₀ d hdpos hdL hP hhom
local notation "Λm" => vacuumWeightNeg k s b M (fun i => RD.pair (RD.iY i) μ)
local notation "Λp" => vacuumWeightPos k s b M (fun i => RD.pair (RD.iY i) μ)

/-- The KL family uses the same block data as the generic vacuum. -/
theorem klRouqFamily_data :
    (klRouqFamily k RD μ s b M d hdpos hd hsym).toRouqData =
      Furling.rouqData Φ
        (coverProduct.{max u v, max u v, 0} (arrowsNeg D) (L := L₀) Λm (arrowsPos D) Λp) D :=
  coverRouqFamily_toRouqData D Λm Λp RD μ
    (coverWeightNeg_finite_fibre (zm k I (Slots s b)) _)
    (coverWeightPos_finite_fibre (zp k I (Slots s b)) _)
    (coverDatum_noCrossArrows P₀ d hdpos hdL hP hhom)
    (generic_base_pair k RD μ s b M P₀ d hdpos hdL hP hhom)
    (coverDatum_finsum_arrows P₀ d hdpos hdL hP hhom C RD (klQ2 L₀ C)
      (kl_factorization k s b) (kl_extremal k s b)) (kl_factorization k s b)

omit [DecidableEq I] in
/-- Standard KL crossing factors descend to the original coefficient field. -/
theorem kl_factor_ground (i j : I) :
    MvPolynomial.map (algebraMap k K₀) (klP2 (k := k) C KL1.stdOrient i j) = P₀ i j :=
  map_klP2 (C := C) (algebraMap k K₀) KL1.stdOrient i j

omit [DecidableEq I] in
/-- In characteristic zero, the positive diagonal Cartan lengths give an
invertible natural symmetrizer for the spectral power series. -/
theorem exists_symmetrizer_of_charZero [CharZero k] :
    ∃ d : I → ℕ, (∀ i, 0 < d i) ∧ (∀ i, (d i : k) ≠ 0) ∧
      ∀ i j, C.dot i j ≠ 0 → (d i : ℤ) * C.dot j j = d j * C.dot i i := by
  refine ⟨fun i => (C.dot i i).toNat, ?_, ?_, ?_⟩
  · intro i
    exact KL3.Diagram.dot_self_toNat_pos i
  · intro i
    have hpos : 0 < (C.dot i i).toNat := by
      have := C.dot_self_pos i
      omega
    exact_mod_cast hpos.ne'
  · intro i j _
    rw [Int.toNat_of_nonneg (C.dot_self_pos i).le,
      Int.toNat_of_nonneg (C.dot_self_pos j).le]
    exact mul_comm _ _

end GenericFields
end Categorification.KLR.Unfurling
