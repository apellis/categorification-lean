/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedHeadEmbedding
import Categorification.WeightedKLR.RedStrands.Vacuum
import Categorification.KLR.CyclotomicAbsentColour

/-!
# The maximal-cut representation in the vacuum

Webster, arXiv:1309.3796v2, Theorem 5.8, for the highest-weight block.
The unique cut has two scalar factors, so every simple there is already
recovered by the vacuum representation.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR Categorification.Graded GProj
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [Field k] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k}
    (Λ : Fin (ℓ+1) → I →₀ ℕ) (G : GradingDatum (stendhalQ Q Λ))

private theorem scalarLayerTower {k C M : Type*} [Field k] [Ring C] [Algebra k C]
    [AddCommGroup M] [Module k M] (σ : C →ₐ[k] k) :
    let := Module.compHom M σ.toRingHom
    IsScalarTower k C M := by
  let := Module.compHom M σ.toRingHom
  exact ⟨fun c a x => by
    change σ (c • a) • x = c • (σ a • x)
    rw [map_smul,smul_assoc]⟩

private def scalarCutEquiv {k B C M : Type*} [Field k] [Ring B] [Ring C]
    [Algebra k B] [Algebra k C] [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]
    (ε : B ≃ₐ[k] k) (σ : C →ₐ[k] k) (ψ : B →ₙₐ[k] C) (hone : σ (ψ 1) = 1) :
    let := Module.compHom M σ.toRingHom
    let := scalarLayerTower (M := M) σ
    M ≃ₗ[B] boundaryFixed ψ M := by
  let := Module.compHom M σ.toRingHom
  let := scalarLayerTower (M := M) σ
  have hact (t : B) (x : M) : ψ t • x = t • x := by
    change σ (ψ t) • x = t • x
    obtain ⟨c,hc⟩ : ∃ c : k, c • (1 : B) = t :=
      ⟨ε t, ε.injective (by rw [map_smul,map_one,smul_eq_mul,mul_one])⟩
    rw [← hc,map_smul,map_smul,hone,smul_eq_mul,mul_one,smul_assoc,one_smul]
  exact
    { toFun := fun x => ⟨x,(hact 1 x).trans (one_smul _ _)⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun t x => Subtype.ext (hact t x).symm }

/-- In the block with no black strands, the vacuum module realizes the
maximal cut for every factor simple (Webster, Theorem 5.8). -/
theorem nonempty_lastRedInducedCut_zero (u : LastRedWeightSplit (0 : Multiset I))
    (b : IndecClass (lastRedFactorGrading Λ 0 G u)) : Nonempty (LastRedInducedCut Λ 0 G u b) := by
  rcases u with ⟨⟨θ,β⟩,hu⟩
  change θ+β=0 at hu
  obtain ⟨rfl,rfl⟩ := add_eq_zero.mp hu
  let u : LastRedWeightSplit (0 : Multiset I) := ⟨(0,0),zero_add _⟩
  let p := LastRedWeightSplit.position 0 u ℓ
  let C := (smallerSuffixIdeal Q Λ p).ringCon.Quotient
  let L := TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (0 : Multiset I)
  let R := CycKLR k Q (fun i => (Polynomial.X : Polynomial k)^Λ (Fin.last ℓ) i) (0 : Multiset I)
  let B := L ⊗[k] R
  let ε : B ≃ₐ[k] k := (Algebra.TensorProduct.congr (tensorProductAlgebraZeroEquiv Q (Λ ∘ Fin.castSucc))
    (KLRAlgebra.cyclotomicZeroEquiv Q _)).trans (Algebra.TensorProduct.lid k k)
  let ψ : B →ₙₐ[k] C := lastRedLayerAction Q Λ p (LastRedWeightSplit.content 0 u ℓ)
    (LastRedWeightSplit.length 0 u ℓ)
  obtain ⟨p',θ,β,h,σ,hs,hl,_,hn⟩ := exists_detecting_lastRedCorner (tensorProductAlgebraZeroEquiv Q Λ).toAlgHom
  obtain ⟨rfl,rfl⟩ := add_eq_zero.mp hs
  have hp : p'=p := Fin.ext (by
    change p'.val = (0 : Multiset I).card + ℓ
    simp [stendhalWeight] at hl ⊢
    omega)
  subst p'
  have he : ψ 1 = lastRedLayerIdem Q Λ p h := congrArg Subtype.val
    (map_one (lastRedLayerTensor Q Λ p h hl))
  have hone : σ (ψ 1) = 1 := by
    have hh := congrArg σ (lastRedLayerIdem_idem Q Λ p h).eq
    rw [map_mul] at hh
    rw [he]
    exact mul_left_cancel₀ hn (hh.trans (mul_one _).symm)
  let : Module C b.top := Module.compHom b.top σ.toRingHom
  let := scalarLayerTower (M := b.top.carrier) σ
  let f := scalarCutEquiv (M := b.top.carrier) ε σ ψ hone
  refine ⟨{carrier := b.top, recover := ⟨f⟩, support := ?_}⟩
  intro v hv
  have hzero : v.1.1 = 0 := (add_eq_zero.mp v.2).1
  exact (hv (show v.1.1 ≤ (0 : Multiset I) by rw [hzero])).elim

end Categorification.Stendhal
