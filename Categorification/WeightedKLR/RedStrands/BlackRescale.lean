/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackAffineProjection
import Categorification.WeightedKLR.RedStrands.TensorRescale

/-!
# Rescaling black crossings commutes with adjoining a black strand

Webster, arXiv:1309.3796v3, §4.6 after Theorem 4.31. Rescaling the black–black crossings of
`T^λ` (`tensorRescale`, §4.2) commutes with Webster's map adjoining a black strand on the right
(`appendBlack`): the crossings of the smaller algebra keep the labels of their two strands.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra MvPolynomial
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} {ℓ : ℕ} [DecidableEq I] [CommRing k]
  {Q Q' : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν : Multiset I)
  {s : I → I → kˣ} (hs : ∀ a, s a a = 1)
  (hQ : ∀ a b, a ≠ b → Q a b = C ((s a b * s b a : kˣ) : k) * Q' a b)

local notation "μ" => stendhalWeight ℓ ν
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "μ'" => stendhalWeight ℓ νᵢ
local notation "hwt" => stendhalWeight_black_cons (ℓ := ℓ) i ν

local notation "S" => affineCoverQ Q Λ
local notation "S'" => affineCoverQ Q' Λ
local notation "r" => rescaleHom (stendhalScale s) (stendhalScale_self hs) (affineCoverQ_rescale hQ)

omit [DecidableEq I] in
private theorem cast_append (t : Seq μ) :
    Seq.cast hwt (Seq.cast (add_comm _ _) (t.append default)) = appendBlackLoading i ν t := by
  apply Subtype.ext
  funext a
  rfl

omit [DecidableEq I] in
theorem crossScale_appendBlackLoading (u : I ⊕ Fin ℓ → I ⊕ Fin ℓ → kˣ) {j : ℕ}
    (hj : j + 1 < Multiset.card μ) (t : Seq μ) :
    crossScale u j (appendBlackLoading i ν t) = crossScale u j t := by
  have hc : Multiset.card μ' = Multiset.card μ + 1 := by simp [stendhalWeight]
  have hj' : j + 1 < Multiset.card μ' := by omega
  rw [crossScale_of_lt u hj', crossScale_of_lt u hj]
  have h1 := appendBlackLoading_lbl_of_lt i ν t ⟨j, by omega⟩ (by simp only []; omega)
  have h2 := appendBlackLoading_lbl_of_lt i ν t ⟨j + 1, hj'⟩ hj
  simp only [Seq.lbl] at h1 h2
  rw [h1, h2]

private theorem cL_sum {R : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k} {ι : Type*}
    (F : Finset ι) (f : ι → KLRAlgebra k R μ) :
    cL R (Sum.inl i) μ (∑ t ∈ F, f t) = ∑ t ∈ F, cL R (Sum.inl i) μ (f t) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, cL_zero]
  | insert a F ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cL_add, ih]

private theorem cast_cL_e {R : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k} (t : Seq μ) :
    castKLR R hwt (cL R (Sum.inl i) μ (e t)) = e (appendBlackLoading i ν t) := by
  rw [cL_e, castKLR_e, cast_append]

private theorem scaleE_mul_cast_cL_one {R : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k}
    (u : I ⊕ Fin ℓ → I ⊕ Fin ℓ → kˣ) {j : ℕ} (hj : j + 1 < Multiset.card μ) :
    scaleE R u j * castKLR R hwt (cL R (Sum.inl i) μ 1) =
      castKLR R hwt (cL R (Sum.inl i) μ (scaleE R u j)) := by
  conv_rhs => rw [scaleE, cL_sum, map_sum]
  rw [← sum_e (k := k) (Q := R) (ν := μ), cL_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [cL_smul, map_smul, cast_cL_e, scaleE_mul_e, crossScale_appendBlackLoading _ _ _ hj]

/-- Rescaling the black crossings commutes with adjoining a black strand on the right, on
the affine cover. -/
theorem rescaleHom_cast_cL (z : KLRAlgebra k S μ) :
    r (castKLR S hwt (cL S (Sum.inl i) μ z)) = castKLR S' hwt (cL S' (Sum.inl i) μ (r z)) := by
  have he (t : Seq μ) : r (castKLR S hwt (cL S (Sum.inl i) μ (e t))) =
      castKLR S' hwt (cL S' (Sum.inl i) μ (r (e t))) := by
    rw [cast_cL_e, rescaleHom_e, rescaleHom_e, cast_cL_e]
  have hone : r (castKLR S hwt (cL S (Sum.inl i) μ 1)) =
      castKLR S' hwt (cL S' (Sum.inl i) μ 1) := by
    rw [← sum_e (k := k) (Q := S) (ν := μ), cL_sum, map_sum, map_sum,
      ← sum_e (k := k) (Q := S') (ν := μ), cL_sum, map_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [he, rescaleHom_e]
  induction z using klr_induction with
  | hr c =>
    rw [Algebra.algebraMap_eq_smul_one, cL_smul, map_smul, map_smul, hone, map_smul, map_one,
      cL_smul, map_smul]
  | hadd x y hx hy => rw [cL_add, map_add, map_add, hx, hy, map_add, cL_add, map_add]
  | hmul x y hx hy => rw [cL_mul, map_mul, map_mul, hx, hy, map_mul, cL_mul, map_mul]
  | he t => exact he t
  | hx a =>
    rw [cL_x, map_mul, map_mul, hone, castKLR_x, rescaleHom_x, rescaleHom_x, cL_x, map_mul,
      castKLR_x]
  | hψ n =>
    by_cases hn : n + 1 < Multiset.card μ
    · rw [cL_ψ _ _ hn, map_mul, map_mul, hone, castKLR_ψ, rescaleHom_ψ, rescaleHom_ψ, rescaleψ,
        rescaleψ, cL_mul, cL_ψ _ _ hn, map_mul, map_mul, castKLR_ψ, mul_assoc, mul_assoc,
        scaleE_mul_cast_cL_one (ℓ := ℓ) (R := S') i ν _ hn, ← map_mul, ← cL_mul, one_mul]
    · rw [ψ_eq_zero n (by omega), cL_zero, map_zero, map_zero, map_zero, cL_zero, map_zero]

/-- **Rescaling black crossings commutes with adjoining a black strand**: Webster's map
`T^λ_ν → T^λ_{ν+i}` of §4.6 intertwines the rescaling isomorphisms `T^λ(Q) ≅ T^λ(Q')`
(`tensorRescale`). -/
theorem tensorRescale_appendBlack (z : TensorProductAlgebra k Q Λ ν) :
    tensorRescale Λ νᵢ hs hQ (appendBlack Q Λ i ν z) =
      appendBlack Q' Λ i ν (tensorRescale Λ ν hs hQ z) := by
  obtain ⟨w, rfl⟩ := affineTensorProjection_surjective (Q := Q) Λ ν z
  rw [appendBlack_affineTensorProjection, tensorRescale_projection, tensorRescale_projection,
    appendBlack_affineTensorProjection, rescaleHom_cast_cL Λ i ν hs hQ]

end Categorification.Stendhal
