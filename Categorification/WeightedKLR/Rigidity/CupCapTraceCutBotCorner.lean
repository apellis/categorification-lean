/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlocksMidBotCorner
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutWindowLoading

/-!
# The bottom corners of the leading Mackey data at `S_+` and at `S_cut`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5.

* At `S_cut` the leading datum has `λ = 0`. Then `1_{0,δ} = 1`, so `quadBot 1` acts on the input
  of the cut through the head factor `1_{α,γ} ⊗ 1` only
  (`quadBot_one_smul_cutInput_of_β_eq_zero`), and the bottom corner is the corner of the input
  cut out by it (`mem_botCorner_cutInput_iff_of_β_eq_zero`).
* At `S_+` the leading datum has weight the window weight. Its colours are those of the middle
  block of `λ⁺` read in the outer labels (`windowColour_eq_comp`, `windowWeight_eq_map`),
  which is the hypothesis `hβ` of `botCornerBlocksEquiv`.

Webster's proof does not spell this out. No new hypothesis.

## Main results

* `Stendhal.concatSet_zero_left`, `Stendhal.quadBot_one_smul_cutInput_of_β_eq_zero`,
  `Stendhal.mem_botCorner_cutInput_iff_of_β_eq_zero`, `Stendhal.CupCap.windowWeight_eq_map`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

theorem concatSet_zero_left {J : Type*} [DecidableEq J] (δ' : Multiset J) :
    concatSet (0 : Multiset J) δ' = Finset.univ := by
  refine Finset.eq_univ_of_forall fun s => ?_
  rw [Seq.mem_concatSet_iff_prefixWt]
  exact Multiset.card_eq_zero.1 (Seq.card_prefixWt s _ _)

theorem castAlg_oneConcat_zero_left {J k : Type*} [DecidableEq J] [CommRing k]
    {P : J → J → MvPolynomial (Fin 2) k} {δ' μ : Multiset J} (h : 0 + δ' = μ) :
    castAlg P h (oneConcat P 0 δ') = 1 := by
  rw [oneConcat, concatSet_zero_left, eSum, sum_e, map_one]

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)
  (Y : Type*) [AddCommGroup Y] [Module k Y] [Module (cutFactorAlgebra Q Λ θ β) Y]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) Y]

variable {ν ν' : Multiset (I ⊕ Fin (a + r))} (q : MackeyQuad ν ν'
  (Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ))
  (Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)))

/-- The head factor `1_{α,γ}` of `quadBot 1` at a cut (Webster v3, Lemma 7.19, trace
half), in `T^A(θ)`. -/
def cutBotHeadIdem : TensorProductAlgebra k Q (Λ ∘ Fin.castAdd r) θ :=
  cutPrefixProjection (a := a) (r := r) Q Λ θ
    (castAlg (stendhalQ Q Λ) q.h₃ (oneConcat (stendhalQ Q Λ) q.α q.γ))

omit [Module k Y] [IsScalarTower k (cutFactorAlgebra Q Λ θ β) Y] in
/-- **`quadBot 1` on the input of a cut when `λ = 0`**: only the head factor `1_{α,γ}` acts. -/
theorem quadBot_one_smul_cutInput_of_β_eq_zero (hβ : q.β = 0) (y : CutInput Q Λ θ β Y) :
    (quadBot (Q := stendhalQ Q Λ) q 1 : TensorKLR (stendhalQ Q Λ) _ _) • y =
      ((cutBotHeadIdem Q Λ θ β q ⊗ₜ (1 : TensorProductAlgebra k Q (Λ ∘ Fin.natAdd a) β) :
        cutFactorAlgebra Q Λ θ β) • (show Y from y) : Y) := by
  obtain ⟨α', β', γ', δ', h₁, h₂, h₃, h₄⟩ := q
  subst hβ
  have h1 : (1 : QuadAlg (stendhalQ Q Λ) ⟨α', 0, γ', δ', h₁, h₂, h₃, h₄⟩) =
      ((1 : KLRAlgebra k (stendhalQ Q Λ) α') ⊗ₜ (1 : KLRAlgebra k (stendhalQ Q Λ) 0)) ⊗ₜ
      ((1 : KLRAlgebra k (stendhalQ Q Λ) γ') ⊗ₜ
        (1 : KLRAlgebra k (stendhalQ Q Λ) δ')) := rfl
  rw [h1, quadBot_tmul, ← Algebra.TensorProduct.one_def, ← Algebra.TensorProduct.one_def,
    concat_one, concat_one, castAlg_oneConcat_zero_left]
  change (cutInputMap Q Λ θ β _) • (show Y from y) = _
  simp only [cutInputMap, Algebra.TensorProduct.map_tmul, map_one]
  rfl

end Categorification.Stendhal

namespace Categorification.Stendhal

open KLR KLRAlgebra

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)
  (Y : Type*) [AddCommGroup Y] [Module k Y] [Module (cutFactorAlgebra Q Λ θ β) Y]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) Y]

variable {ν ν' : Multiset (I ⊕ Fin (a + r))} (q : MackeyQuad ν ν'
  (Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ))
  (Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)))

/-- **The bottom corner at a cut when `λ = 0`** is the corner of the input cut out by the head
factor `1_{α,γ} ⊗ 1`. -/
theorem mem_botCorner_cutInput_iff_of_β_eq_zero (hβ : q.β = 0) (y : CutInput Q Λ θ β Y) :
    y ∈ botCorner (stendhalQ Q Λ) q (CutInput Q Λ θ β Y) ↔
      ((cutBotHeadIdem Q Λ θ β q ⊗ₜ (1 : TensorProductAlgebra k Q (Λ ∘ Fin.natAdd a) β) :
        cutFactorAlgebra Q Λ θ β) • (show Y from y) : Y) = y := by
  rw [mem_botCorner, quadBot_one_smul_cutInput_of_β_eq_zero Q Λ θ β Y q hβ]
  exact Iff.rfl

end Categorification.Stendhal

namespace Categorification.Stendhal.CupCap

variable {I : Type} {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)

/-- The colours of the window are those of the middle block of `λ⁺` read in its three
blocks. -/
theorem windowColour_eq_comp :
    windowColour (I := I) j hj = Sum.map (id : I → I) (Fin.natAdd j) ∘
      Sum.map (id : I → I) (Fin.castAdd (ℓ - j)) := by
  funext x
  rcases x with b | u
  · rfl
  · simp only [windowColour, Function.comp_apply, Sum.map_inr]
    congr 1

/-- **The window weight is the weight of the middle block**, read in the outer labels. -/
theorem windowWeight_eq_map (ν₀ : Multiset I) :
    (stendhalWeight 2 ν₀).map (windowColour j hj) =
      ((stendhalWeight 2 ν₀).map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j)))).map
        (Sum.map (id : I → I) (Fin.natAdd j)) := by
  rw [Multiset.map_map, windowColour_eq_comp]

end Categorification.Stendhal.CupCap
