/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AffineCoverGrading
import Categorification.WeightedKLR.RedStrands.TensorProjection
import Categorification.KLR.CyclotomicDividedProjectives

/-!
# Integral generation by divided Stendhal projectives

Webster, arXiv:1309.3796v2, Lemma 4.37. Project the ordinary affine divided
words to the ordered violating quotient. Each red label has multiplicity one,
so all blocks of size greater than one consist of black strands.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR QuantumGroup KLRAlgebra Categorification.Graded StendhalAlgebraAllOrders MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ)
  (C : CartanDatum I) (hQ : IsRouquierQ C Q) (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "Aff" => KLRAlgebra k (affineCoverQ Q Λ) μ
local notation "T" => TensorProductAlgebra k Q Λ ν

local notation "π" => affineTensorProjection (Q := Q) Λ ν
local notation "di" => fun i => C.dot i i / 2
omit [DecidableEq I] in
private theorem dotDegree (i : I) : hQ.gradingDatum.degX i = 2 * (C.dot i i / 2) := by
  change C.dot i i = _
  obtain ⟨n, hn⟩ := C.dot_self_even i
  omega
local notation "hdi" => dotDegree C hQ
local notation "H" => affineCoverGrading Λ hQ.gradingDatum di hdi
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum di hdi
local notation "𝓡" => GradingDatum.grade H μ
local notation "𝓣" => tensorProductGrade G ν
local notation "C'" => affineCoverCartan C ℓ
local notation "hs" => affineCoverGrading_cross_symm Λ hQ.gradingDatum di hdi
  (fun i j => congrArg Neg.neg (C.symm i j))

private theorem projection_graded : PreservesGrading 𝓡 𝓣 (π).toLinearMap := by
  intro n x hx
  apply Graded.mem_map_of_mem
  change affineCover Q Λ ν x * redOrderedIdem k Q Λ ν ∈ allOrdersGrade G ν n
  have he : redOrderedIdem k Q Λ ν ∈ allOrdersGrade G ν 0 :=
    Submodule.sum_mem _ fun i _ => Graded.mem_map_of_mem _ _ ((G).e_mem_grade i)
  simpa only [add_zero] using SetLike.GradedMul.mul_mem (A := allOrdersGrade G ν)
    (affineCover_mem_grade Λ hQ.gradingDatum di hdi ν hx) he

local instance : Module Affᵐᵒᵖ T := Module.compHom T (π).toRingHom.op
local instance : SMulCommClass T Affᵐᵒᵖ T where
  smul_comm b r x := (mul_assoc b x (π r.unop)).symm
local instance : IsScalarTower k Affᵐᵒᵖ T where
  smul_assoc c r x := by
    change x * π (c • r.unop) = c • (x * π r.unop)
    rw [map_smul, mul_smul_comm]

private def projectionK0 : K0 𝓡 →ₗ[LaurentPolynomial ℤ] K0 𝓣 :=
  extensionK0 𝓡 𝓣 π (projection_graded Λ C hQ ν) (fun _ _ => rfl)

/-- Webster's divided-word projective, obtained by applying the ordered
violating quotient to the nilHecke idempotent and retaining its Cartan shift. -/
def dividedSequenceProj (w : List ((I ⊕ Fin ℓ) × ℕ)) (hw : (expandDiv w : Multiset _) = μ) :
    GProj 𝓣 :=
  let t := Seq.ofList (expandDiv w) hw
  let p : Aff := hflip (divIdem t (blocksDiv w 0))
  (GProj.ofIdempotent (𝒜 := 𝓣) (π p)
    ((isIdempotentElem_hflip_divIdem (isBlocks_ofList w hw)).map (π))
    (projection_graded Λ C hQ ν ((H).hflip_mem_grade hs
      (divIdem_mem_grade H (isBlocks_ofList w hw))))).shift (-KL2.divAngle2 C' w)

theorem projectionK0_dividedProjective (w : List ((I ⊕ Fin ℓ) × ℕ)) (hw : (expandDiv w : Multiset _) = μ) :
    projectionK0 Λ C hQ ν (K0.of ((H).dividedProjective hs C' w hw)) =
      K0.of (dividedSequenceProj Λ C hQ ν w hw) := by
  unfold KLR.GradingDatum.dividedProjective dividedSequenceProj
  rw [← K0.T_smul_of, map_smul, ← K0.T_smul_of]
  congr 1
  exact extensionK0_ofIdempotent 𝓡 𝓣 π (projection_graded Λ C hQ ν) (fun _ _ => rfl) _ _

/-- Webster, arXiv:1309.3796v2, Lemma 4.37. The shifted divided-word
projectives span the graded projective Grothendieck group over the Laurent
integers for every red family, black multiset and Rouquier parameter over a field. -/
theorem span_dividedSequenceProj :
    Submodule.span (LaurentPolynomial ℤ) {z | ∃ (w : List ((I ⊕ Fin ℓ) × ℕ))
      (hw : (expandDiv w : Multiset _) = μ), z = K0.of (dividedSequenceProj Λ C hQ ν w hw)} = ⊤ := by
  have hX := affineCoverGrading_dot Λ hQ.gradingDatum di hdi C (fun _ => rfl)
  have hsym := affineCoverQ_symm Λ (fun i j hij => (hQ.symm i j hij).symm)
  have hn := affineCoverQ_ne_zero (Q := Q) Λ (fun i j hij h => by have u := hQ.unit_coeff i j hij; simp [h] at u)
  let := (H).hasGdim_grade' (ν := μ) hsym (fun i => (hX i).symm ▸ (C').dot_self_pos i)
  have surj := extensionK0_surjective 𝓡 𝓣 π (projection_graded Λ C hQ ν) (fun _ _ => rfl)
    (affineTensorProjection_surjective (Q := Q) Λ ν)
  apply top_unique
  rw [← LinearMap.range_eq_top.mpr (show Function.Surjective (projectionK0 Λ C hQ ν) from surj),
    ← Submodule.map_top, ← (H).span_dividedProjective hs C' μ hX hsym hn, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨w, hw, projectionK0_dividedProjective Λ C hQ ν w hw⟩

end Categorification.Stendhal
