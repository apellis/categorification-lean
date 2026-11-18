/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverSequenceClass
import Categorification.WeightedKLR.RedStrands.RestrictionExtension

/-!
# Normalized black restriction on Stendhal sequence projectives

Webster, arXiv:1309.3796v2, §4.6 and Lemmas 4.35–4.36. On a sequence
projective, restriction projects the normalized cyclotomic deletion sum.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra CycKLR QuantumGroup QuantumGroup.UDot Categorification.Graded
open LieLean.QuantumGroup

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k}
  (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I) (hQ : IsRouquierQ C Q) (ν : Multiset I)
  (i : I)

local notation "D" => I ⊕ Fin ℓ
local notation "μ" => stendhalWeight ℓ ν
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "γ" => ((Singleton.singleton (Sum.inl i) : Multiset D) + μ)
local notation "S" => cyclotomicCoverQ C Λ Q
local notation "p" => cyclotomicCoverPolynomial (I := I) (ℓ := ℓ) (k := k)
local notation "m" => cyclotomicCoverExponent (I := I) (ℓ := ℓ)
local notation "q" => (fun j : D => (Polynomial.X : Polynomial k) ^ m j)
local notation "hq" => Eq.symm (cyclotomicCoverPolynomial_eq_pow (I := I) (ℓ := ℓ) (k := k))
local notation "hS" => isRouquierQ_cyclotomicCoverQ C Λ Q hQ
local notation "H" => IsRouquierQ.gradingDatum hS
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum
  (fun j => C.dot j j / 2) (dotDegree C hQ)
local notation "C₀" => extendedCartanDatum C Λ
local notation "φ" => cyclotomicCoverToTensor (Q := Q) Λ ν C
local notation "φ'" => cyclotomicCoverUpper (Q := Q) Λ ν C i
local notation "LP" => LaurentPolynomial ℤ

private theorem powerCoverMap_eq_cast :
    powerCoverMap (Q := Q) Λ C ν = (coverPolynomialCast S hq μ).toAlgHom := by
  apply CycKLR.algHom_ext
  apply AlgHom.ext
  intro a
  change powerCoverMap (Q := Q) Λ C ν (CycKLR.mk k S q μ a) = _
  rw [powerCoverMap, CycKLR.lift_mk]
  exact (coverPolynomialCast_mk S hq μ a).symm

omit [DecidableEq I] in
private theorem cast_ofList {J : Type*} {u v : Multiset J} (h : u = v)
    (s : List J) (hs : (s : Multiset J) = u) :
    Seq.cast h (Seq.ofList s hs) = Seq.ofList s (hs.trans h) := by
  subst v
  rfl

private theorem upper_power_boundary (w : List D) (hw : (w : Multiset D) = γ)
    (ho : IsRedOrdered (Seq.ofList w (hw.trans (stendhalWeight_black_cons i ν)))) :
    φ' (coverPolynomialCast S hq γ (CycKLR.mk k S q γ (e (Seq.ofList w hw)))) =
      TensorProductAlgebra.mk Q Λ νᵢ
        (StendhalAlgebra.e (Seq.ofList w (hw.trans (stendhalWeight_black_cons i ν))) ho) := by
  rw [coverPolynomialCast_mk]
  unfold cyclotomicCoverUpper
  change cyclotomicCoverToTensor (Q := Q) Λ νᵢ C
    (CyclotomicAction.castCyc S p (stendhalWeight_black_cons i ν)
      (CycKLR.mk k S p γ (e (Seq.ofList w hw)))) = _
  rw [CyclotomicAction.castCyc_mk, castKLR_e, cast_ofList]
  exact cyclotomicCoverToTensor_mk_e Λ C νᵢ _ ho

private theorem restriction_principal_congr
    {a b : TensorProductAlgebra k Q Λ νᵢ} (hab : a = b)
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (ha₀ : a ∈ tensorProductGrade G νᵢ 0) (hb₀ : b ∈ tensorProductGrade G νᵢ 0) :
    K0.of (blackResProj G i ν C hQ (GProj.ofIdempotent a ha ha₀)) =
      K0.of (blackResProj G i ν C hQ (GProj.ofIdempotent b hb hb₀)) := by
  subst b
  rfl

/-- Normalized black restriction has the marked deletion formula on every
ordered sequence projective, with the quotient class at each remaining
loading. -/
theorem blackRaiseK0_projectedSequenceClass (w : List D) (hw : (w : Multiset D) = γ)
    (ho : IsRedOrdered (Seq.ofList w (hw.trans (stendhalWeight_black_cons i ν)))) :
    blackRaiseK0 G i ν C hQ
      (projectedSequenceClass Λ C hQ νᵢ (Seq.ofList w (hw.trans (stendhalWeight_black_cons i ν)))) =
      (((markedWords w).attach).map fun t =>
        if hi : Sum.inl i = t.1.2.1 then
          qIntU (qUnitLP ^ di C₀ (Sum.inl i)) (prefixPair C₀ m (Sum.inl i) t.1.1) •
            projectedSequenceClass Λ C hQ ν
              (Seq.ofList (t.1.1 ++ t.1.2.2) (markedBlackDeletionContent ν hw t.2 hi))
        else 0).sum := by
  let s := Seq.ofList w hw
  let es := CycKLR.mk k S q γ (e s)
  have he : IsIdempotentElem es := (show IsIdempotentElem (e (Q := S) s) from e_mul_self s).map _
  have he₀ : es ∈ CycKLR.grade H m γ 0 := Graded.mem_map_of_mem _ _ ((H).e_mem_grade s)
  rw [← cyclotomicCoverPowerProjectionK0_raise_sequenceProjective Λ C hQ ν i w hw,
    raiseK0, LinearMap.smul_apply, map_smul, cyclotomicCover_raiseShift Λ C ν i,
    projectedSequenceClass_ordered Λ C hQ νᵢ _ ho, blackRaiseK0, LinearMap.smul_apply, resK0_of]
  congr 1
  unfold cyclotomicCoverPowerProjectionK0 coverExtensionK0
  let f := (φ).comp (powerCoverMap (Q := Q) Λ C ν)
  let := coverRightModule f
  let := coverSmulComm f
  let := coverScalarTower f
  have h := extensionK0_restriction_leftIdeal Λ ν C i m hq hQ
    f (powerCoverToTensor_graded Λ C hQ ν)
    (fun _ _ => rfl) (congrArg (AlgHom.comp φ) (powerCoverMap_eq_cast Λ C ν)) he he₀
  rw [h, blackResK0_of]
  have hb := upper_power_boundary (Q := Q) Λ C ν i w hw ho
  change φ' (coverPolynomialCast S hq γ es) = _ at hb
  exact (restriction_principal_congr Λ C hQ ν i hb _ _ _ _).symm

end Categorification.Stendhal
