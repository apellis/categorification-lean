/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorCoefficientConcentratedCover
import Categorification.WeightedKLR.Rigidity.SMoveLeftStdUpperIdem
import Categorification.WeightedKLR.RedStrands.LeftStandardTensorFixedInjective
import Categorification.WeightedKLR.Rigidity.SMoveDiagonalTorZeroSummand

/-!
# Higher Tor of the diagonal pair, reduced to free inputs

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c), step R5 (higher Tor of the diagonal pair). The coefficient of the
diagonal pair is `W^r` for `W = 𝕊^{λ_1; λ_2, λ_3}(P_∅ ⊠ S(M))` (`SMove.leftStd`), `S(M)` the
standardization of a finite-dimensional factor module `M`, and the module is the standard
`S_s` of a loading `s` with every black strand left of the last red strand (on the diagonal,
`s = (red₁ red₂ 𝐮 red₃)`).

Cover `M` by a free module, `0 → K → D^{n+1} → M → 0` with `K` finite-dimensional
(`exists_stdLayer_freeCover`); standardization, `SMove.leftStd` and the reflection are exact, so
this gives a short exact sequence of coefficients `0 → W_K^r → W_{free}^r → W^r → 0` of the same
kind. On `Tor₀` against `S_s` the map `W_K^r ⊗ S_s → W_{free}^r ⊗ S_s` is injective: both
coefficients are killed by the loading idempotents above `s`
(`SMove.op_seqIdem_smul_reflectOne_leftStd_eq_zero_of_stendhalLT`), and on such coefficients
tensoring with `S_s` preserves injectivity (`injective_tensorProductOver_map_leftStandard`). The
dimension shift of `isZero_derivedTensorHomology_of_concentratedCoefficientCovers` then reduces
the vanishing of the higher Tor of `W^r` against `S_s` to the free inputs.

Route hypothesis: `hfree`, the vanishing of the higher Tor of `W_{free}^r` against `S_s` for the
free inputs `D^{n+1}` (to be supplied by a standard filtration of `W_{free}`: the partial
standardization of a two-strand standard is a three-strand standard). A Rouquier choice of `Q`
(finite-dimensionality of the factor algebras, for the covers).

## Main results

* `SMove.leftStdReflectTensorEquivFixed`: `W^r ⊗_T S_s ≅ W^r e(s)`.
* `SMove.isZero_derivedTensorHomology_reflectOne_leftStd_stdLayer_of_free`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.SMove

open CategoryTheory CategoryTheory.Limits KLR Equiv MulOpposite BraidedStendhalAlgebra
open DG DG.DerivedCategory
open scoped DG.DegreeZero

universe w

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) (Λ : Fin (1 + (1 + 1)) → I →₀ ℕ) {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight (1 + (1 + 1)) ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ)
  [HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q Λ ν)] [HasDerivedCategory.{w, 0} ℤ]

local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "Λ₂₃" => (Λ ∘ Fin.natAdd 1 : Fin (1 + 1) → I →₀ ℕ)

/-- The coefficient `W^r` of the diagonal pair for an input `N` over `T^{λ_2, λ_3}(ν)`. -/
abbrev leftStdReflect (N : ModuleCat.{0} (TensorProductAlgebra k Q Λ₂₃ ν)) :
    ModuleCat.{0} Tᵐᵒᵖ :=
  (reflectOne (ℓ := 1 + 1) Q Λ hQ hρ).obj ((leftStd Q hQ Λ ν).obj N)

omit [HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q Λ ν)] [HasDerivedCategory.{w, 0} ℤ] in
/-- The scalars of `k` commute with a right `T`-module structure. -/
theorem smulCommClass_leftStdReflect (N : ModuleCat.{0} (TensorProductAlgebra k Q Λ₂₃ ν)) :
    SMulCommClass k Tᵐᵒᵖ (leftStdReflect Q hQ Λ hρ N) :=
  IsScalarTower.to_smulCommClass

attribute [local instance] smulCommClass_leftStdReflect

omit [HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q Λ ν)] [HasDerivedCategory.{w, 0} ℤ] in
/-- **`Tor₀` of the diagonal pair is a corner** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22, `Tor₀` of the diagonal pair): for every input `N` and every loading `s` with
all black strands left of the last red strand, `W^r ⊗_T S_s ≅ W^r e(s)` for
`W = SMove.leftStd N`, through `leftStandardTensorEquivFixed`. No route hypotheses. -/
def leftStdReflectTensorEquivFixed (N : ModuleCat.{0} (TensorProductAlgebra k Q Λ₂₃ ν))
    (s : Seq (stendhalWeight (1 + (1 + 1)) ν)) (hs : IsRedOrdered s)
    (hlast : ∀ i, blackCount s (Fin.last 2) i = ν.count i) :
    BalancedTensor k k T (leftStdReflect Q hQ Λ hρ N) (leftStandard Q Λ s hs) ≃ₗ[k]
      fixSub k (leftStdReflect Q hQ Λ hρ N) (op (seqIdem Q Λ s hs)) :=
  leftStandardTensorEquivFixed Q Λ s hs _ fun t ht hst x =>
    op_seqIdem_smul_reflectOne_leftStd_eq_zero_of_stendhalLT Q hQ Λ ν hρ N s hlast t ht hst x

/-- **Higher Tor of the diagonal pair from free inputs** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.22, gap (c), step R5): let `s` be a loading of the three red strands with
every black strand left of the last red strand, `S_s` its standard module. If the coefficients
`W^r = (SMove.leftStd S(D^{n+1}))^r` of the free inputs `D^{n+1}` of a split `θ + β = ν` have
no higher Tor against `S_s`, then neither has `W^r` for `S(M)`, `M` any finite-dimensional
factor module of that split.

Route hypotheses: a Rouquier choice of `Q`; `hfree` (the free inputs). -/
theorem isZero_derivedTensorHomology_reflectOne_leftStd_stdLayer_of_free
    {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q) {θ β : Multiset I} (h : θ + β = ν)
    (s : Seq (stendhalWeight (1 + (1 + 1)) ν)) (hs : IsRedOrdered s)
    (hlast : ∀ i, blackCount s (Fin.last 2) i = ν.count i)
    (hfree : ∀ (n : ℕ) (m : ℤ), m ≠ 0 → IsZero ((homologyFunctor (A := ℤ) ℤ m).obj
      ((derivedTensor.{w} ℤ T (leftStdReflect Q hQ Λ hρ
        (stdOf Q Λ₂₃ hQ h (Fin (n + 1) → parabolicFactorAlgebra Q Λ₂₃ θ β)))).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor T).obj
          (ModuleCat.of T (leftStandard Q Λ s hs)))))))
    (M : FactorModule Q Λ₂₃ θ β) [FiniteDimensional k M.carrier] (m : ℤ) (hm : m ≠ 0) :
    IsZero ((homologyFunctor (A := ℤ) ℤ m).obj
      ((derivedTensor.{w} ℤ T (leftStdReflect Q hQ Λ hρ
        (stdLayerModule Q Λ₂₃ hQ ⟨θ, β, h, M⟩))).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor T).obj
          (ModuleCat.of T (leftStandard Q Λ s hs)))))) := by
  let 𝒞 : ModuleCat.{0} Tᵐᵒᵖ → Prop := fun N => ∃ (K : FactorModule Q Λ₂₃ θ β)
    (_ : FiniteDimensional k K.carrier),
      Nonempty (N ≅ leftStdReflect Q hQ Λ hρ (stdLayerModule Q Λ₂₃ hQ ⟨θ, β, h, K⟩))
  -- The coefficients of the class are killed by the loading idempotents above `s`.
  have hkill : ∀ (X : ModuleCat.{0} (TensorProductAlgebra k Q Λ₂₃ ν))
      (t : Seq (stendhalWeight (1 + (1 + 1)) ν)) (ht : IsRedOrdered t), StendhalLT s t →
      ∀ x : leftStdReflect Q hQ Λ hρ X, op (seqIdem Q Λ t ht) • x = 0 :=
    fun X t ht hst x =>
      op_seqIdem_smul_reflectOne_leftStd_eq_zero_of_stendhalLT Q hQ Λ ν hρ X s hlast t ht hst x
  refine isZero_derivedTensorHomology_of_concentratedCoefficientCovers
    (ModuleCat.of T (leftStandard Q Λ s hs)) 𝒞 ?_ _ ⟨M, inferInstance, ⟨Iso.refl _⟩⟩ m hm
  rintro N ⟨K, hK, ⟨eN⟩⟩
  obtain ⟨n, K', hK', S, hS, h₁, h₂, h₃⟩ := exists_stdLayer_freeCover Q Λ₂₃ hQ hR h K
  let F : ModuleCat.{0} (TensorProductAlgebra k Q Λ₂₃ ν) ⥤ ModuleCat.{0} Tᵐᵒᵖ :=
    leftStd Q hQ Λ ν ⋙ reflectOne (ℓ := 1 + 1) Q Λ hQ hρ
  have : F.PreservesZeroMorphisms := by dsimp only [F]; infer_instance
  have hS' : (S.map F).ShortExact :=
    shortExact_map_reflectOne (ℓ := 1 + 1) Q Λ hQ hρ
      (ModuleExactFunctor.shortExact_map (moduleExactFunctor_leftStd Q hQ Λ ν) hS)
  refine ⟨S.map F, hS', ⟨K', hK', ⟨eqToIso (by rw [ShortComplex.map_X₁, h₁]; rfl)⟩⟩, ?_, ?_,
    ⟨eqToIso (by rw [ShortComplex.map_X₃, h₃]; rfl) ≪≫ eN.symm⟩⟩
  · intro j hj
    have hX₂ : (S.map F).X₂ = leftStdReflect Q hQ Λ hρ
        (stdOf Q Λ₂₃ hQ h (Fin (n + 1) → parabolicFactorAlgebra Q Λ₂₃ θ β)) := by
      rw [ShortComplex.map_X₂, h₂]; rfl
    rw [hX₂]
    exact hfree n j hj
  · apply mono_homology_derivedTensorCoefficientMap_of_injective
    have hf : Function.Injective (S.map F).f.hom :=
      (ModuleCat.mono_iff_injective _).mp hS'.mono_f
    exact injective_tensorProductOver_map_leftStandard Q Λ s hs _ _
      (hkill (S.X₁)) (hkill (S.X₂)) (S.map F).f.hom hf
