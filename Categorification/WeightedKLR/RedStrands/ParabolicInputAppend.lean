/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicLastStrand
import Categorification.WeightedKLR.RedStrands.SingleRedInduction
import Categorification.KLR.IndLastStrand

/-!
# The two input quotients of standardization and the last black strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. Standardization with two pieces induces from `R(α) ⊗ R(δ)`, where `α` carries
the first `ℓ` red strands and `δ` the last red strand followed by black strands; the input
module is a module over `T^{λ'} ⊗ R^{λ_ℓ}`, reached by the quotients
`parabolicPrefixProjection` and `parabolicLastCyclotomic`. Both quotients commute with adjoining
a black strand on the right: on the prefix this is Webster's `appendBlack`, on the last factor
it is the last-strand map `cyclotomicLast` of the cyclotomic quotient (Theorem 4.20).

## Main results

* `parabolicPrefixProjection_appendR`;
* `parabolicLastCyclotomic_appendR`.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (wt : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ : Multiset I)

local notation "last" => (fun _ : Fin 1 => Fin.last ℓ)
local notation "lastColour" => Sum.map (id : I → I) last
local notation "S" => stendhalQ Q wt
local notation "θᵢ" => ((Singleton.singleton i : Multiset I) + θ)
local notation "aΛ" => fun j => (Polynomial.X : Polynomial k) ^ wt (Fin.last ℓ) j
local notation "Aₚ" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "Aₗ" => Multiset.map lastColour (stendhalWeight 1 θ)

omit [DecidableEq I] in
/-- Adjoining the black weight `i` to the prefix weight. -/
theorem prefixWeight_addBlack :
    Aₚ + {Sum.inl i} = Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θᵢ) :=
  map_stendhalWeight_addBlack Fin.castSucc i θ

omit [DecidableEq I] in
/-- Adjoining the black weight `i` to the last-factor weight. -/
theorem lastWeight_addBlack :
    Aₗ + {Sum.inl i} = Multiset.map lastColour (stendhalWeight 1 θᵢ) :=
  map_stendhalWeight_addBlack (fun _ : Fin 1 => Fin.last ℓ) i θ

/-- The prefix quotient commutes with adjoining a black strand on the right. -/
theorem parabolicPrefixProjection_appendR (w : KLRAlgebra k S Aₚ) :
    parabolicPrefixProjection Q wt θᵢ
        (castKLR S (prefixWeight_addBlack i θ) (appendR S Aₚ (Sum.inl i) w)) =
      appendBlack Q (wt ∘ Fin.castSucc) i θ (parabolicPrefixProjection Q wt θ w) := by
  rw [appendR_apply]
  exact redSubfamilyProjection_appendBlack Q wt Fin.castSucc (Fin.castSucc_injective ℓ) i θ w

/-- The last-factor quotient `R(δ) → R^{λ_ℓ}` commutes with adjoining a black strand on the
right, through the cyclotomic last-strand map. -/
theorem parabolicLastCyclotomic_appendR (w : KLRAlgebra k S Aₗ) :
    parabolicLastCyclotomic Q wt θᵢ
        (castKLR S (lastWeight_addBlack i θ) (appendR S Aₗ (Sum.inl i) w)) =
      AbsentColour.cyclotomicLast Q i aΛ θ (parabolicLastCyclotomic Q wt θ w) := by
  apply (SingleRed.cyclotomicEquiv Q (fun _ : Fin 1 => wt (Fin.last ℓ)) θᵢ).injective
  rw [← SingleRed.appendBlack_cyclotomicEquiv]
  simp only [parabolicLastCyclotomic, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply]
  rw [appendR_apply]
  exact redSubfamilyProjection_appendBlack Q wt (fun _ : Fin 1 => Fin.last ℓ)
    (fun _ _ _ => Subsingleton.elim _ _) i θ w

end Categorification.Stendhal
