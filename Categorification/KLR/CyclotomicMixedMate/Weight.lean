/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.CyclotomicMixedMate.Lower

/-!
# The upper accepted crossing comparison

`upperAcceptedCorner` transports the accepted crossing corner to the original
rectangular corner; both upper inclusions and support cuts are preserved.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.AbsentColour.MixedComparison
open MulOpposite MixedTransport MixedMate
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)

@[simp] theorem weightEquiv_trans {β δ ε : Multiset I} (h : β = δ) (g : δ = ε)
    (x : CycKLR k Q a β) :
    weightEquiv Q a g (weightEquiv Q a h x) = weightEquiv Q a (h.trans g) x := by
  subst δ; subst ε; rfl
@[simp] theorem weightEquiv_symm {β δ : Multiset I} (h : β = δ) :
    (weightEquiv Q a h).symm = weightEquiv Q a h.symm := by
  subst δ; rfl

theorem weightEquiv_last {β δ : Multiset I} (h : β = δ) (c : I)
    (x : CycKLR k Q a β) :
    weightEquiv Q a (congrArg ({c} + ·) h) (cyclotomicLast Q c a β x) =
      cyclotomicLast Q c a δ (weightEquiv Q a h x) := by
  subst δ; rfl

variable (γ : Multiset I) (i j : I)
local notation "V" => CycKLR k Q a
  ((Singleton.singleton j : Multiset I) + ((Singleton.singleton i : Multiset I) + γ))

def upperWeight : CycKLR k Q a ((γ + {j}) + {i}) ≃ₐ[k] V :=
  weightEquiv Q a (by ac_rfl)

theorem upperWeight_left (b : CycKLR k Q a (γ + {j})) :
    upperWeight Q a γ i j (MixedCyclotomic.quotientInc Q a (γ + {j}) i b) =
      leftInc Q a γ i j (lowerWeight Q a γ j b) := by
  change weightEquiv Q a _ _ =
    (κ Q a γ i j).symm (cyclotomicLast Q i a ({j} + γ) (lowerWeight Q a γ j b))
  rw [← weightEquiv_last Q a (add_comm γ ({j} : Multiset I)),
    last_eq_weight_inc, κ, weightEquiv_symm, weightEquiv_trans, weightEquiv_trans]

theorem quotientBot_eq (b : CycKLR k Q a (γ + {i})) :
    MixedCyclotomic.quotientBotLinear Q γ i j a b =
      weightEquiv Q a (MixedAffine.weightSquare γ i j)
        (MixedCyclotomic.quotientInc Q a (γ + {i}) j b) := by
  obtain ⟨b, rfl⟩ := CycKLR.mk_surjective b
  rw [MixedCyclotomic.quotientBotLinear_mk, MixedCyclotomic.quotientInc_mk, weightEquiv_mk]
  rfl

theorem upperWeight_right (b : CycKLR k Q a (γ + {i})) :
    upperWeight Q a γ i j (MixedCyclotomic.quotientBotLinear Q γ i j a b) =
      cyclotomicLast Q j a ({i} + γ) (lowerWeight Q a γ i b) := by
  change weightEquiv Q a _ _ = _
  rw [quotientBot_eq, ← weightEquiv_last Q a (add_comm γ ({i} : Multiset I)),
    last_eq_weight_inc, weightEquiv_trans, weightEquiv_trans]

theorem quotient_left_unit :
    MixedCyclotomic.quotientInc Q a (γ + {j}) i 1 =
      CycKLR.mk k Q a ((γ + {j}) + {i}) (oneConcat Q (γ + {j}) {i}) := by
  rw [← map_one (CycKLR.mk k Q a (γ + {j})), MixedCyclotomic.quotientInc_mk]
  congr 1
  exact concat_one_tmul_one

theorem quotient_right_unit :
    MixedCyclotomic.quotientBotLinear Q γ i j a 1 =
      CycKLR.mk k Q a ((γ + {j}) + {i}) (botOne Q (MixedAffine.weightSquare γ i j)) := by
  rw [← map_one (CycKLR.mk k Q a (γ + {i})), MixedCyclotomic.quotientBotLinear_mk]
  exact congrArg (CycKLR.mk k Q a ((γ + {j}) + {i}))
    (botConcat_one (Q := Q) (h := MixedAffine.weightSquare γ i j))

theorem upperWeight_mem (z : CycKLR k Q a ((γ + {j}) + {i})) :
    z ∈ MixedCyclotomic.quotientCornerSub Q γ i j a ↔
      upperWeight Q a γ i j z ∈ cornerSub Q a γ i j := by
  change _ * z * _ = z ↔ _ * upperWeight Q a γ i j z = _ ∧
    upperWeight Q a γ i j z * _ = _
  rw [← quotient_left_unit, ← quotient_right_unit]
  have hl := upperWeight_left Q a γ i j (1 : CycKLR k Q a (γ + {j}))
  have hr := upperWeight_right Q a γ i j (1 : CycKLR k Q a (γ + {i}))
  simp only [map_one] at hl hr
  rw [← (upperWeight Q a γ i j).injective.eq_iff, map_mul, map_mul, hl, hr]
  let l := leftInc Q a γ i j 1
  let r := cyclotomicLast Q j a ({i} + γ) 1
  have hll : l * l = l := by
    change leftInc Q a γ i j 1 * leftInc Q a γ i j 1 = leftInc Q a γ i j 1
    rw [← map_mul, one_mul]
  have hrr : r * r = r := by
    change cyclotomicLast Q j a ({i} + γ) 1 * cyclotomicLast Q j a ({i} + γ) 1 =
      cyclotomicLast Q j a ({i} + γ) 1
    rw [← map_mul, one_mul]
  constructor
  · intro h
    constructor
    · calc
        l * upperWeight Q a γ i j z = l * (l * upperWeight Q a γ i j z * r) :=
          congrArg (l * ·) h.symm
        _ = l * upperWeight Q a γ i j z * r := by rw [← mul_assoc, ← mul_assoc, hll]
        _ = upperWeight Q a γ i j z := h
    · calc
        upperWeight Q a γ i j z * r = (l * upperWeight Q a γ i j z * r) * r :=
          congrArg (· * r) h.symm
        _ = l * upperWeight Q a γ i j z * r := by rw [mul_assoc, hrr]
        _ = upperWeight Q a γ i j z := h
  · rintro ⟨hl, hr⟩
    rw [hl, hr]

/-- The accepted rectangular corner in the original reversed upper weight. -/
def upperAcceptedCorner : MixedCyclotomic.QuotientCorner Q γ i j a ≃ₗ[k] Corner Q a γ i j where
  toFun z := ⟨upperWeight Q a γ i j z.1, (upperWeight_mem Q a γ i j z.1).1 z.2⟩
  invFun z := ⟨(upperWeight Q a γ i j).symm z.1, by
    apply (upperWeight_mem Q a γ i j _).2
    rw [AlgEquiv.apply_symm_apply]; exact z.2⟩
  left_inv z := Subtype.ext ((upperWeight Q a γ i j).symm_apply_apply z.1)
  right_inv z := Subtype.ext ((upperWeight Q a γ i j).apply_symm_apply z.1)
  map_add' z t := Subtype.ext (map_add _ _ _)
  map_smul' c z := Subtype.ext (map_smul _ _ _)

end Categorification.KLR.KLRAlgebra.AbsentColour.MixedComparison
