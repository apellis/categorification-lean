/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastOuter
import Categorification.KLR.IndLastStrandDescent

/-!
# The last-strand sequence of standardization

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. Write `θ = i + θ₀`, `β = i + β₀`, and let `e` be the idempotent of the
parabolic shuffle module (the image of `1_{-,i}`) whose image is the part on which the last
strand is a black strand labelled `i`. For a module `N` over `T^{λ'}(θ) ⊗ R^{λ_ℓ}(β)` there is
a short exact sequence of `k`-modules

`0 → S(₂E_i N) → (S N)ᵉ → S(₁E_i N) → 0`,

where `S` is standardization (`ParabolicStandard`), `₂E_i N` and `₁E_i N` are the restrictions
of `N` along `1 ⊗ cyclotomicLast` and `appendBlack ⊗ 1`, and `(S N)ᵉ` is the quotient of the
shuffle module by the kernel of `P e`, `P` the red-ordered idempotent
(`lastStandardTwo_injective`, `lastStandard_exact`, `lastStandardOne_surjective`). The middle
term is the `e`-fixed part of `S N` (`lastStandardMiddleEquiv`).

Gradings are not modelled.

## Main results

* `IdempotentQuotient.descendLinearEquiv`: a linear isomorphism intertwining `p` and `q`
  induces `X / ker p ≃ M / ker q`.
* `lastStandardTwo_injective`, `lastStandard_exact`, `lastStandardOne_surjective`.
* `lastStandardMiddleEquiv`.
-/

noncomputable section

/-- Exactness is preserved by composing with linear isomorphisms on all three terms. -/
theorem Function.Exact.conj_linearEquiv {R : Type*} [CommRing R] {A X B A' X' B' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup X] [Module R X] [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A'] [AddCommGroup X'] [Module R X'] [AddCommGroup B']
    [Module R B'] {f : A →ₗ[R] X} {g : X →ₗ[R] B} (h : Function.Exact f g)
    (a : A' ≃ₗ[R] A) (x : X ≃ₗ[R] X') (b : B ≃ₗ[R] B') :
    Function.Exact (x.toLinearMap ∘ₗ f ∘ₗ a.toLinearMap) (b.toLinearMap ∘ₗ g ∘ₗ
      x.symm.toLinearMap) := by
  intro y
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Set.mem_range]
  rw [b.map_eq_zero_iff, h (x.symm y)]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨a.symm u, by rw [LinearEquiv.apply_symm_apply, hu, LinearEquiv.apply_symm_apply]⟩
  · rintro ⟨u, hu⟩
    exact ⟨a u, by rw [← hu, LinearEquiv.symm_apply_apply]⟩

namespace Categorification

namespace IdempotentQuotient

open Submodule LinearMap

variable {R : Type*} [CommRing R] {X M : Type*} [AddCommGroup X] [Module R X] [AddCommGroup M]
  [Module R M] (p : X →ₗ[R] X) (q : M →ₗ[R] M) (g : X ≃ₗ[R] M)
  (hg : ∀ x, g (p x) = q (g x))

/-- A linear isomorphism `g` with `g ∘ p = q ∘ g` induces `X / ker p ≃ M / ker q`. -/
def descendLinearEquiv : (X ⧸ ker p) ≃ₗ[R] (M ⧸ ker q) :=
  { descend p q g.toLinearMap hg with
    invFun := descend q p g.symm.toLinearMap (fun m => by
      apply g.injective
      rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hg, LinearEquiv.apply_symm_apply])
    left_inv := fun z => by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      change descend q p _ _ (descend p q _ _ _) = _
      rw [descend_mk, descend_mk, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
    right_inv := fun z => by
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      change descend p q _ _ (descend q p _ _ _) = _
      rw [descend_mk, descend_mk, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] }

theorem descendLinearEquiv_mk (x : X) :
    descendLinearEquiv p q g hg (Submodule.Quotient.mk x) = Submodule.Quotient.mk (g x) := rfl

end IdempotentQuotient

namespace Stendhal

open KLR KLRAlgebra IdempotentQuotient
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ₀ β₀ : Multiset I)

local notation "last" => (fun _ : Fin 1 => Fin.last ℓ)
local notation "lastColour" => Sum.map (id : I → I) last
local notation "S" => stendhalQ Q Λ
local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "Aₚ" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ₀)
local notation "Aₗ" => Multiset.map lastColour (stendhalWeight 1 β₀)
local notation "hA" => prefixWeight_addBlack (ℓ := ℓ) i θ₀
local notation "hD" => lastWeight_addBlack (ℓ := ℓ) i β₀
local notation "θ" => ((Si i) + θ₀)
local notation "β" => ((Si i) + β₀)
local notation "j" => (Sum.inl i : I ⊕ Fin (ℓ + 1))
local notation "P" => eSum S (redOrderedSet (Aₚ + {j} + (Aₗ + {j})))
local notation "P₂" => eSum S (redOrderedSet (Aₚ + {j} + Aₗ))
local notation "e₁" => lastIdem S Aₚ Aₗ j

-- `{i}` rather than the `Si` notation: notation is not hygienic inside `variable` binders.
variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N]

local notation "N₁" => LastInput Q Λ i θ₀ β₀ N
local notation "Er" => LastResRight Q Λ i θ₀ β₀ N
local notation "El" => LastResLeft Q Λ i θ₀ β₀ N
local notation "L" => Algebra.lsmul k k (Ind S (Aₚ + {j}) (Aₗ + {j}) N₁)
local notation "Lt" => Algebra.lsmul k k (Ind S (Aₚ + {j}) Aₗ (ResRight S (Aₚ + {j}) Aₗ j N₁))
local notation "Lo" => Algebra.lsmul k k (Ind S Aₚ (Aₗ + {j}) (ResAppendL S Aₚ Aₗ j N₁))

theorem lastP₂_mul :
    P * e₁ = castKLR S (add_assoc (Aₚ + {j}) Aₗ {j}) (appendR S (Aₚ + {j} + Aₗ) j P₂) :=
  eSum_redOrderedSet_mul_lastIdem Aₚ Aₗ i

/-- The image of `1_{-,i}` in the parabolic shuffle module. -/
abbrev lastShuffleIdem : Module.End k (ParabolicShuffle Q Λ θ β N) :=
  parabolicShuffleAction Q Λ θ β N (castKLR S (lastShuffle_weight i θ₀ β₀) e₁)

/-- The red-ordered idempotent on the parabolic shuffle module. -/
abbrev lastShuffleOrdered (a b : Multiset I) (M : Type*) [AddCommGroup M] [Module k M]
    [Module (parabolicFactorAlgebra Q Λ a b) M]
    [IsScalarTower k (parabolicFactorAlgebra Q Λ a b) M] :
    Module.End k (ParabolicShuffle Q Λ a b M) :=
  parabolicShuffleAction Q Λ a b M (eSum S (parabolicOrderedLoadings (ℓ := ℓ) a b))

/-- **The middle term**, transported to the parabolic shuffle module. -/
def lastMiddleEquiv :
    (Ind S (Aₚ + {j}) (Aₗ + {j}) N₁ ⧸ LinearMap.ker (L P * L e₁)) ≃ₗ[k]
      (ParabolicShuffle Q Λ θ β N ⧸
        LinearMap.ker (lastShuffleOrdered Q Λ θ β N * lastShuffleIdem Q Λ i θ₀ β₀ N)) :=
  descendLinearEquiv _ _ (lastShuffleEquiv Q Λ i θ₀ β₀ N) fun y => by
    simp only [Module.End.mul_apply, Algebra.lsmul_coe, lastShuffleEquiv_smul,
      castKLR_eSum_redOrderedSet_eq_parabolicOrderedLoadings]

/-- **The submodule term** `S(₂E_i N)`. -/
def lastTwoEquiv :
    (Ind S (Aₚ + {j}) Aₗ (ResRight S (Aₚ + {j}) Aₗ j N₁) ⧸ LinearMap.ker (Lt P₂)) ≃ₗ[k]
      ParabolicStandard Q Λ θ β₀ Er :=
  descendLinearEquiv _ _ (lastOuterRightEquiv Q Λ i θ₀ β₀ N) fun y => by
    simp only [Algebra.lsmul_coe, lastOuterRightEquiv, indCast_smul, castKLR_eSum_redOrderedSet,
      parabolicOrderedLoadings_eq_redOrderedSet]

/-- **The quotient term** `S(₁E_i N)`. -/
def lastOneEquiv :
    (Ind S Aₚ (Aₗ + {j}) (ResAppendL S Aₚ Aₗ j N₁) ⧸ LinearMap.ker (Lo (lastIdemOne P₂))) ≃ₗ[k]
      ParabolicStandard Q Λ θ₀ β El :=
  descendLinearEquiv _ _ (lastOuterLeftEquiv Q Λ i θ₀ β₀ N) fun y => by
    simp only [Algebra.lsmul_coe, lastOuterLeftEquiv, indCast_smul, lastIdemOne,
      castKLR_eSum_redOrderedSet, parabolicOrderedLoadings_eq_redOrderedSet]

variable (hQ : KLRSymm Q)

/-- **The inclusion** `S(₂E_i N) → (S N)ᵉ`. -/
def lastStandardTwo :
    ParabolicStandard Q Λ θ β₀ Er →ₗ[k]
      (ParabolicShuffle Q Λ θ β N ⧸
        LinearMap.ker (lastShuffleOrdered Q Λ θ β N * lastShuffleIdem Q Λ i θ₀ β₀ N)) :=
  (lastMiddleEquiv Q Λ i θ₀ β₀ N).toLinearMap ∘ₗ
    lastDescendTwo (N := N₁) (lastP₂_mul Q Λ i θ₀ β₀) ∘ₗ
      (lastTwoEquiv Q Λ i θ₀ β₀ N).symm.toLinearMap

/-- **The projection** `(S N)ᵉ → S(₁E_i N)`. -/
def lastStandardOne :
    (ParabolicShuffle Q Λ θ β N ⧸
        LinearMap.ker (lastShuffleOrdered Q Λ θ β N * lastShuffleIdem Q Λ i θ₀ β₀ N)) →ₗ[k]
      ParabolicStandard Q Λ θ₀ β El :=
  (lastOneEquiv Q Λ i θ₀ β₀ N).toLinearMap ∘ₗ
    lastDescendOne (N := N₁) (stendhalQ_swap_symm Q Λ hQ) (lastP₂_mul Q Λ i θ₀ β₀) ∘ₗ
      (lastMiddleEquiv Q Λ i θ₀ β₀ N).symm.toLinearMap

include hQ in
theorem lastStandardTwo_injective :
    Function.Injective (lastStandardTwo Q Λ i θ₀ β₀ N) := by
  simp only [lastStandardTwo, LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact (lastMiddleEquiv Q Λ i θ₀ β₀ N).injective.comp
    ((lastDescend_injective (stendhalQ_swap_symm Q Λ hQ) _).comp
      (lastTwoEquiv Q Λ i θ₀ β₀ N).symm.injective)

theorem lastStandardOne_surjective :
    Function.Surjective (lastStandardOne Q Λ i θ₀ β₀ N hQ) := by
  simp only [lastStandardOne, LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact (lastOneEquiv Q Λ i θ₀ β₀ N).surjective.comp
    ((lastDescend_surjective _ _).comp (lastMiddleEquiv Q Λ i θ₀ β₀ N).symm.surjective)

theorem lastStandard_exact :
    Function.Exact (lastStandardTwo Q Λ i θ₀ β₀ N) (lastStandardOne Q Λ i θ₀ β₀ N hQ) :=
  (lastDescend_exact (hP := eSum_idem _) (hc := commute_eSum_redOrderedSet_lastIdem Aₚ Aₗ i)
    (hsym := stendhalQ_swap_symm Q Λ hQ) (hP₂ := lastP₂_mul Q Λ i θ₀ β₀)).conj_linearEquiv _ _ _

end Stendhal

end Categorification
