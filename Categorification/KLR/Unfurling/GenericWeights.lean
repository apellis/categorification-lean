/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.GenericFields

/-!
# Generic cover weights with separate strand and bubble labels

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
proof of the theorem labelled `nondegenerate`, construction of representations.
The finite multiplicities below realize a prescribed base pairing, with level
`M` at every strand label and level one at additional bubble labels. Separating
these labels retains the high cyclotomic truncation needed for the strands,
without raising the bubble parameters to the characteristic-dependent power
`M`. A balancing label realizes the remaining positive or negative weight.

The fields and all labels are constructed, not supplied as hypotheses. The KLR
polynomial parameters in `vacuum_noCrossArrows` and `vacuum_finsum_base` remain
explicit: their specialization to KL parameters is a separate input.
-/

noncomputable section
namespace Categorification.KLR.Unfurling.GenericFields

/-- Disjoint alphabets for strand labels, level-one bubble labels and a balancing label. -/
abbrev Slots (s b : ℕ) := Fin s ⊕ (Fin b ⊕ Unit)

variable {I : Type*}

/-- Negative levels: strand level `M`, bubble level one, and the negative part of the weight. -/
def negLevel (s b M : ℕ) (h : I → ℤ) (i : I) : Slots s b → ℕ
  | .inl _ => M
  | .inr (.inl _) => 1
  | .inr (.inr _) => (-h i).toNat

/-- Positive levels, with the positive part of the desired weight at the balancing label. -/
def posLevel (s b M : ℕ) (h : I → ℤ) (i : I) : Slots s b → ℕ
  | .inl _ => M
  | .inr (.inl _) => 1
  | .inr (.inr _) => (h i).toNat

/-- The two levels have precisely the prescribed weight difference. -/
theorem sum_level_difference (s b M : ℕ) (h : I → ℤ) (i : I) :
    ∑ q : Slots s b, ((posLevel s b M h i q : ℤ) - negLevel s b M h i q) = h i := by
  simp [Slots, Fintype.sum_sum_type, negLevel, posLevel]

variable (k : Type*) [Field k] (s b M : ℕ) (h : I → ℤ)

/-- The concrete negative weight. -/
def vacuumWeightNeg := weightNeg k I (Slots s b) (negLevel s b M h)

/-- The concrete positive weight. -/
def vacuumWeightPos := weightPos k I (Slots s b) (posLevel s b M h)

@[simp] theorem vacuumWeightNeg_strand (i : I) (q : Fin s) :
    vacuumWeightNeg k s b M h ⟨i, zm k I (Slots s b) i (.inl q)⟩ = M := by
  exact weightNeg_mk k I (Slots s b) _ i (.inl q)

@[simp] theorem vacuumWeightPos_strand (i : I) (q : Fin s) :
    vacuumWeightPos k s b M h ⟨i, zp k I (Slots s b) i (.inl q)⟩ = M := by
  exact weightPos_mk k I (Slots s b) _ i (.inl q)

@[simp] theorem vacuumWeightNeg_bubble (i : I) (q : Fin b) :
    vacuumWeightNeg k s b M h ⟨i, zm k I (Slots s b) i (.inr (.inl q))⟩ = 1 := by
  exact weightNeg_mk k I (Slots s b) _ i (.inr (.inl q))

@[simp] theorem vacuumWeightPos_bubble (i : I) (q : Fin b) :
    vacuumWeightPos k s b M h ⟨i, zp k I (Slots s b) i (.inr (.inl q))⟩ = 1 := by
  exact weightPos_mk k I (Slots s b) _ i (.inr (.inl q))

variable (P₀ : I → I → MvPolynomial (Fin 2) (K k (I × Slots s b)))
  (d : I → ℕ) (hdpos : ∀ i, 0 < d i)
  (hd : ∀ i, ((d i : ℕ) : L k (I × Slots s b) (I × Slots s b)) ≠ 0)
  (hP : ∀ i j, i ≠ j → MvPolynomial.map
    (algebraMap (K k (I × Slots s b)) (L k (I × Slots s b) (I × Slots s b))) (P₀ i j) ≠ 0)
  (hhom : ∀ i j, i ≠ j → ∃ D, (MvPolynomial.map
    (algebraMap (K k (I × Slots s b)) (L k (I × Slots s b) (I × Slots s b)))
      (P₀ i j)).IsWeightedHomogeneous ![d j, d i] D)

/-- The concrete generic fields discharge the separation of the two parts of the cover.
Polynomial factorization and homogeneity are the separate KLR-parameter input. -/
theorem vacuum_noCrossArrows : NoCrossArrows (coverDatum P₀ d hdpos hd hP hhom) :=
  coverDatum_noCrossArrows P₀ d hdpos hd hP hhom

/-- Concrete generic weights supply the base pairing required for furling. -/
theorem vacuum_finsum_base (i : I) :
    ∑ᶠ a : {a // (coverDatum P₀ d hdpos hd hP hhom).π a = i},
      coverBaseVal (vacuumWeightNeg k s b M h) (vacuumWeightPos k s b M h) a.1 = h i := by
  exact (coverDatum_finsum_base P₀ d hdpos hd hP hhom (zm k I (Slots s b))
    (zp k I (Slots s b)) (negLevel s b M h) (posLevel s b M h) i).trans
    (sum_level_difference s b M h i)

end Categorification.KLR.Unfurling.GenericFields
