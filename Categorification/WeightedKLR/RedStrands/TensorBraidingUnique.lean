/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorBraiding

/-!
# Maps out of `A ⊗ V^w ⊗ C` commuting with the `F_i`

Let `A` and `C` be representations of `U_q(𝔤)` and `V^w` a simple highest weight module, with
`U_q(𝔤)` acting on `(A ⊗ V^w) ⊗ C` through the coproduct. Two linear maps out of it which
commute with every `F_i` and agree on the vectors `(a ⊗ v_w) ⊗ c` are equal (`ext_tripleRep`).
This is the uniqueness step in the proof of Webster, arXiv:1309.3796v2, Corollary 6.10
(v3: Corollary 6.11): the pure tensors with the highest weight vector in one factor generate
the ordered tensor product under the `F_i`. The proof is by induction on the length of an
`F`-word applied to `v_w`; the other factors are arbitrary, since `K̃_i^{-1}` is invertible on
`C` and acts on weight vectors of `V^w` by scalars.

## Main results

* `tripleRep_F`: the action of `F_i` on `(a ⊗ y) ⊗ c`.
* `span_wordVec`: `V^w` is spanned by the vectors `F_{i_1} ⋯ F_{i_n} v_w`.
* `ext_tripleRep`: the uniqueness statement.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open scoped TensorProduct

local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local instance : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y}

local notation "𝕌" => LieLean.QuantumGroup R 𝕍
local notation "Δ" => comul R 𝕍

private abbrev Fac (w : Dom R) := IrreducibleModule R 𝕍 w.1

/-! ### `F`-words on the highest weight vector -/

/-- The vector `F_{i_1} ⋯ F_{i_n} v_w` of `V^w`, for the word `l = [i_1, …, i_n]`. -/
def wordVec (w : Dom R) (l : List I) : Fac w :=
  (VermaModule.maxSubmodule R 𝕍 w.1).mkQ (VermaModule.toVerma R 𝕍 w.1 (LusztigF.monomial 𝕂 l))

theorem wordVec_nil (w : Dom R) : wordVec w [] = IrreducibleModule.hwv R 𝕍 w.1 := by
  rw [wordVec, LusztigF.monomial, List.map_nil, List.prod_nil, VermaModule.toVerma_apply,
    map_one, one_smul]
  rfl

theorem wordVec_cons (w : Dom R) (j : I) (l : List I) :
    wordVec w (j :: l) = F R 𝕍 j • wordVec w l := by
  rw [wordVec, wordVec, LusztigF.monomial_cons, VermaModule.toVerma_apply, map_mul, mul_smul,
    minusHom_θ, ← VermaModule.toVerma_apply, LinearMap.map_smul]

theorem wordVec_mem_weightSpace (w : Dom R) (l : List I) :
    wordVec w l ∈ weightSpace R 𝕍 (Fac w) (w.1 - R.rootSum (LusztigF.wordWeight l)) := by
  have h := VermaModule.toVerma_mem_weightSpace (R := R) (v := 𝕍) (Λ := w.1)
    (Submodule.subset_span ⟨l, rfl, rfl⟩ :
      LusztigF.monomial 𝕂 l ∈ LusztigF.weightSpace 𝕂 (LusztigF.wordWeight l))
  intro μ
  rw [wordVec, ← LinearMap.map_smul, h μ, LinearMap.map_smul_of_tower]

theorem span_wordVec (w : Dom R) : Submodule.span 𝕂 (Set.range (wordVec w)) = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ y
  have hv : v ∈ LinearMap.range (VermaModule.toVerma R 𝕍 w.1) := by
    rw [VermaModule.range_toVerma]; trivial
  obtain ⟨x, rfl⟩ := hv
  have hx : x ∈ Submodule.span 𝕂 (Set.range (LusztigF.monomial 𝕂 (I := I))) := by
    rw [LusztigF.span_monomial]; trivial
  let φ : LusztigF 𝕂 I →ₗ[𝕂] Fac w :=
    ((VermaModule.maxSubmodule R 𝕍 w.1).mkQ.restrictScalars 𝕂) ∘ₗ VermaModule.toVerma R 𝕍 w.1
  have := Submodule.mem_map_of_mem (f := φ) hx
  rw [Submodule.map_span, ← Set.range_comp] at this
  exact this

/-! ### Three blocks -/

variable {A L C N : Type*} [AddCommGroup A] [Module 𝕂 A] [AddCommGroup L] [Module 𝕂 L]
  [Module (LieLean.QuantumGroup R 𝕍) L] [IsScalarTower 𝕂 (LieLean.QuantumGroup R 𝕍) L]
  [AddCommGroup C] [Module 𝕂 C] [AddCommGroup N]
  [Module 𝕂 N]

variable (L) in
/-- The action of `U` on `(A ⊗ L) ⊗ C` through the coproduct. -/
def tripleRep (actA : 𝕌 →ₐ[𝕂] Module.End 𝕂 A) (actC : 𝕌 →ₐ[𝕂] Module.End 𝕂 C) :
    𝕌 →ₐ[𝕂] Module.End 𝕂 ((A ⊗[𝕂] L) ⊗[𝕂] C) :=
  (pairRep ((pairRep actA (Algebra.lsmul 𝕂 𝕂 L : 𝕌 →ₐ[𝕂] _)).comp Δ) actC).comp Δ

variable (actA : LieLean.QuantumGroup R 𝕍 →ₐ[𝕂] Module.End 𝕂 A)
  (actC : LieLean.QuantumGroup R 𝕍 →ₐ[𝕂] Module.End 𝕂 C)

theorem tripleRep_F (i : I) (a : A) (y : L) (c : C) :
    tripleRep L actA actC (F R 𝕍 i) ((a ⊗ₜ[𝕂] y) ⊗ₜ[𝕂] c) =
      (actA (F R 𝕍 i) a ⊗ₜ[𝕂] (K R 𝕍 (-ktilde R i) • y)) ⊗ₜ[𝕂]
          actC (K R 𝕍 (-ktilde R i)) c +
        (a ⊗ₜ[𝕂] (F R 𝕍 i • y)) ⊗ₜ[𝕂] actC (K R 𝕍 (-ktilde R i)) c +
        (a ⊗ₜ[𝕂] y) ⊗ₜ[𝕂] actC (F R 𝕍 i) c := by
  simp only [tripleRep, AlgHom.comp_apply, comul_F, map_add, LinearMap.add_apply,
    pairRep_tmul, map_one, Module.End.one_apply, Algebra.lsmul_coe,
    TensorProduct.add_tmul]

/-- Two linear maps out of `(A ⊗ L) ⊗ C` commuting with the `F_i` agree, if they agree on
the vectors `(a ⊗ v []) ⊗ c`, where `v` is a family of weight vectors of `L` spanning `L` with
`v (j :: l) = F_j v l`. -/
theorem ext_tripleRep (actN : 𝕌 →ₐ[𝕂] Module.End 𝕂 N) (f g : (A ⊗[𝕂] L) ⊗[𝕂] C →ₗ[𝕂] N)
    (hf : ∀ (i : I) (z : (A ⊗[𝕂] L) ⊗[𝕂] C),
      f (tripleRep L actA actC (F R 𝕍 i) z) = actN (F R 𝕍 i) (f z))
    (hg : ∀ (i : I) (z : (A ⊗[𝕂] L) ⊗[𝕂] C),
      g (tripleRep L actA actC (F R 𝕍 i) z) = actN (F R 𝕍 i) (g z))
    (v : List I → L) (hv_cons : ∀ j l, v (j :: l) = F R 𝕍 j • v l)
    (hv_wt : ∀ l, ∃ Λ, v l ∈ weightSpace R 𝕍 L Λ)
    (hv_span : Submodule.span 𝕂 (Set.range v) = ⊤)
    (h : ∀ (a : A) (c : C), f ((a ⊗ₜ[𝕂] v []) ⊗ₜ[𝕂] c) = g ((a ⊗ₜ[𝕂] v []) ⊗ₜ[𝕂] c)) :
    f = g := by
  have hS : ∀ (i : I) (z : (A ⊗[𝕂] L) ⊗[𝕂] C), z ∈ LinearMap.eqLocus f g →
      tripleRep L actA actC (F R 𝕍 i) z ∈ LinearMap.eqLocus f g := fun i z hz ↦ by
    rw [LinearMap.mem_eqLocus] at hz ⊢
    rw [hf, hg, hz]
  have key : ∀ (l : List I) (a : A) (c : C),
      (a ⊗ₜ[𝕂] v l) ⊗ₜ[𝕂] c ∈ LinearMap.eqLocus f g := by
    intro l
    induction l with
    | nil => exact h
    | cons j l ih =>
      intro a c
      obtain ⟨Λ, hΛ⟩ := hv_wt l
      set c' := actC (K R 𝕍 (ktilde R j)) c
      have hc : actC (K R 𝕍 (-ktilde R j)) c' = c := by
        rw [← Module.End.mul_apply, ← map_mul, K_add, neg_add_cancel, K_zero, map_one,
          Module.End.one_apply]
      have h₁ := hS j _ (ih a c')
      have h₂ := Submodule.smul_mem (LinearMap.eqLocus f g) (𝕍 ^ Λ (-ktilde R j) : 𝕂)
        (ih (actA (F R 𝕍 j) a) (actC (K R 𝕍 (-ktilde R j)) c'))
      have h₃ := ih a (actC (F R 𝕍 j) c')
      have := (LinearMap.eqLocus f g).sub_mem ((LinearMap.eqLocus f g).sub_mem h₁ h₂) h₃
      rw [tripleRep_F, hΛ, hc] at this
      simp only [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul'] at this
      rw [hv_cons]
      convert this using 1
      abel
  refine TensorProduct.ext_threefold fun a y c ↦ ?_
  have hy : y ∈ Submodule.span 𝕂 (Set.range v) := by rw [hv_span]; trivial
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨l, rfl⟩ := hy; exact key l a c
  | zero => simp
  | add y y' _ _ hy hy' => rw [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add, map_add,
      hy, hy']
  | smul s y _ hy => rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', map_smul,
      map_smul, hy]

end Categorification.Stendhal.FirstWeight
