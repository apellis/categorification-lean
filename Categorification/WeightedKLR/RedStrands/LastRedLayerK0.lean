/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedLayerGrading
import Categorification.WeightedKLR.RedStrands.LastRedLayerClasses
import Categorification.Algebra.Graded.ExtensionK0

/-!
# Projective classes on a last-red layer

For a fixed split of black content, the graded surjection of layer algebras
in the filtration of Webster, arXiv:1309.3796v2, §4.7 induces a surjection
on graded projective Grothendieck groups.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR Categorification.Graded
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ)
  {ν θ β : Multiset I} (G : GradingDatum (stendhalQ Q Λ))
  (p : Fin (stendhalWeight (ℓ+1) ν).card)
  (h : stendhalWeight (ℓ+1) θ + β.map Sum.inl = stendhalWeight (ℓ+1) ν)
  (ha : (stendhalWeight (ℓ+1) θ).card = p.val+1)
local notation "L" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ
local notation "Rfin" => CycKLR k Q (fun i => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β
local notation "B" => (L ⊗[k] Rfin)
local notation "Layer" => IsIdempotentElem.Corner (lastRedLayerIdem_idem Q Λ p h)
local instance : Ring Layer := _root_.instRingCorner _ _
local notation "φ" => lastRedLayerTensor Q Λ p h ha
local notation "𝓑" => tensorGrading (tensorProductGrade (restrictRedGrading Q Λ G) θ)
  (CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) β)
local notation "𝓛" => lastRedLayerCornerGrade Q Λ G p h
/-- Extension from the tensor product of the earlier red block and the final
cyclotomic block to the last-red layer corner. -/
def lastRedLayerK0 : K0 (A := B) 𝓑 →ₗ[LaurentPolynomial ℤ] K0 (A := Layer) 𝓛 := by
  let : Module Bᵐᵒᵖ Layer := Module.compHom Layer (φ).toRingHom.op
  let : SMulCommClass Layer Bᵐᵒᵖ Layer := ⟨fun r a x => (mul_assoc r x (φ a.unop)).symm⟩
  let : IsScalarTower k Bᵐᵒᵖ Layer := ⟨fun a r x => by
    change x * φ (a • r.unop) = a • (x * φ r.unop)
    rw [map_smul, mul_smul_comm]⟩

  exact extensionK0 𝓑 𝓛 φ (fun _ _ hz => lastRedLayerTensor_mem_grade Q Λ G p h ha hz) (fun _ _ => rfl)

/-- Every graded projective class of this layer corner has a lift to the two
independent factors over any field with Rouquier parameters. -/
theorem lastRedLayerK0_surjective {C : QuantumGroup.CartanDatum I} (hQ : IsRouquierQ C Q) :
    Function.Surjective (lastRedLayerK0 Q Λ G p h ha) := by
  let := lastRedLayerSource_finite hQ (Λ ∘ Fin.castSucc) θ (Λ (Fin.last ℓ)) β
  let := HasGdim.of_finiteDimensional 𝓑
  unfold lastRedLayerK0
  let : Module Bᵐᵒᵖ Layer := Module.compHom Layer (φ).toRingHom.op
  let : SMulCommClass Layer Bᵐᵒᵖ Layer := ⟨fun r a x => (mul_assoc r x (φ a.unop)).symm⟩
  let : IsScalarTower k Bᵐᵒᵖ Layer := ⟨fun a r x => by
    change x * φ (a • r.unop) = a • (x * φ r.unop)
    rw [map_smul, mul_smul_comm]⟩

  exact extensionK0_surjective 𝓑 𝓛 φ _ _ (lastRedLayerTensor_surjective Q Λ p h ha)

end Categorification.Stendhal
