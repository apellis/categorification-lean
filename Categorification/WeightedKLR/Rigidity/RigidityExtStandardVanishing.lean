/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtLevels
import Categorification.WeightedKLR.Rigidity.RigidityExtStandardExt
import Categorification.Algebra.ExtVanishingShift

/-!
# Ext between standardizations and dual standard modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1, proof
of Proposition 7.8. Let `S_c(N)` be the standardization of a module `N` over the factor algebra of
a split `c = (θ, β)`, whose loadings have their last red strand at position `|θ| + ℓ`. Let
`∇(t, u) = S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u))^⋆` be a dual standard module, at position `|θ'| + ℓ`.

## Main results

* `subsingleton_ext_stdLayer_starDual_standard`: `Extʲ(S_c(N), ∇(t, u)) = 0` when
  `|θ| < |θ'| + j`, by the injective coresolution of `∇(t, u)` dual to Proposition 7.6.
* `subsingleton_hom_loadingProj`: no maps `T^λ e(s) → Y` when `e(s)` kills `Y`.
* `stdShortComplex_shortExact`: standardization takes short exact sequences of factor modules to
  short exact sequences.
-/

noncomputable section
namespace Categorification

namespace Stendhal

open KLR KLRAlgebra CategoryTheory CategoryTheory.Abelian

universe w

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {ν : Multiset I}

local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "σT" => (tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν : T ≃+* Tᵐᵒᵖ)

/-- If `e(s)` kills `Y`, there are no nonzero maps `T^λ e(s) → Y`. -/
theorem subsingleton_hom_loadingProj {Y : ModuleCat.{0} T} (s : Seq (stendhalWeight (ℓ + 1) ν))
    (hs : IsRedOrdered s) (hY : ∀ y : Y, loadingIdem Q Λ s hs • y = 0) :
    Subsingleton (loadingProj Q Λ s hs ⟶ Y) := by
  have hzero : ∀ f : loadingProj Q Λ s hs ⟶ Y, f = 0 := by
    intro f
    have he : loadingIdem Q Λ s hs * loadingIdem Q Λ s hs = loadingIdem Q Λ s hs :=
      isIdempotentElem_mk_e s hs
    let e₀ : loadingProj Q Λ s hs :=
      (⟨loadingIdem Q Λ s hs, he⟩ : lIdeal (loadingIdem Q Λ s hs))
    have h1 : f.hom e₀ = 0 := by
      have h2 : e₀ = loadingIdem Q Λ s hs • e₀ := Subtype.ext he.symm
      rw [h2, LinearMap.map_smul]
      exact hY _
    ext x
    have hx : x = (show lIdeal (loadingIdem Q Λ s hs) from x).1 • e₀ :=
      Subtype.ext ((show lIdeal (loadingIdem Q Λ s hs) from x).2.symm)
    change f.hom x = 0
    rw [hx, LinearMap.map_smul, h1, smul_zero]
  exact ⟨fun f g => (hzero f).trans (hzero g).symm⟩

section Dual

variable (Q Λ) (hQ : KLRSymm Q) {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
  (hall : AllFiniteDeltaInjective Q Λ hQ)
  [HasExt.{w} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν))]

include hR hall in
/-- **Ext from a standardization into a dual standard module**: for the standardization of a
module over the factor algebra of `θ + β` and the dual standard `∇(t, u)` of a split `θ' + u`,
`Extʲ(S(N), ∇(t, u)) = 0` as soon as `|θ| < |θ'| + j`. Under the route hypothesis `hall` of
Proposition 7.6. -/
theorem subsingleton_ext_stdLayer_starDual_standard (c : StdLayer Q Λ ν) {θ' : Multiset I}
    (t : Seq (stendhalWeight ℓ θ')) (ht : IsRedOrdered t) (u : List I)
    (h : θ' + wordWt u 0 = ν) (j : ℕ) (hj : Multiset.card c.θ < Multiset.card θ' + j) :
    Subsingleton (Ext.{w} (stdLayerModule Q Λ hQ c) (starDualObj k σT
      (tensorStd Q Λ hQ h (oldProj Q Λ θ' t ht) (cycWord Q Λ u))) j) := by
  refine subsingleton_ext_starDual_standard_of_killed Q Λ hQ hR hall t ht u h _ j ?_
  intro s hs hmem
  have hlen : (t.word.map (addRedColor ℓ)).length = Multiset.card θ' + ℓ := by
    rw [List.length_map, Seq.length_word]; simp [stendhalWeight]
  have hlt : Multiset.card θ' + ℓ + j < Multiset.card (stendhalWeight (ℓ + 1) ν) := by
    obtain ⟨Tm, hT, hw⟩ := Multiset.mem_map.1 hmem
    have hlen' := congrArg List.length hw
    rw [Seq.length_word] at hlen'
    rw [← hlen', websterWord]
    have := length_pickIn u.reverse (Multiset.mem_powersetCard.1 hT).1
    simp only [List.length_append, List.length_map, List.length_reverse, List.length_singleton,
      hlen, this, (Multiset.mem_powersetCard.1 hT).2]
    omega
  exact killedAfter_stdLayerModule Q Λ hQ c s hs ⟨_, hlt⟩ (by simp only; omega)
    (lbl_of_word_eq_websterWord hmem _ (by simp only [hlen]))

end Dual

section ShortExact

variable (Q Λ) (hQ : KLRSymm Q) {θ β : Multiset I} (h : θ + β = ν)

/-- The standardization `0 → S(N₁) → S(N₂) → S(N₃) → 0` of a sequence of factor modules. -/
def stdShortComplex {N₁ N₂ N₃ : FactorModule Q Λ θ β}
    (f : N₁.carrier →ₗ[parabolicFactorAlgebra Q Λ θ β] N₂.carrier)
    (g : N₂.carrier →ₗ[parabolicFactorAlgebra Q Λ θ β] N₃.carrier) (hfg : g.comp f = 0) :
    ShortComplex (ModuleCat.{0} T) :=
  ShortComplex.mk (ModuleCat.ofHom (stdLayerMap Q Λ hQ h f))
    (ModuleCat.ofHom (stdLayerMap Q Λ hQ h g)) (by
      ext x
      have key := LinearMap.congr_fun (parabolicStandardMap_comp Q Λ θ β f g)
        (x : ParabolicStandard Q Λ θ β N₁.carrier)
      rw [hfg, parabolicStandardMap_zero] at key
      exact key.symm)

/-- **Standardization is exact on short exact sequences.** -/
theorem stdShortComplex_shortExact {N₁ N₂ N₃ : FactorModule Q Λ θ β}
    (f : N₁.carrier →ₗ[parabolicFactorAlgebra Q Λ θ β] N₂.carrier)
    (g : N₂.carrier →ₗ[parabolicFactorAlgebra Q Λ θ β] N₃.carrier) (hfg : g.comp f = 0)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g) :
    (stdShortComplex Q Λ hQ h f g hfg).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact parabolicStandardMap_exact Q Λ θ β hQ f g hex
  · exact (ModuleCat.mono_iff_injective _).mpr (parabolicStandardMap_injective Q Λ θ β hQ f hf)
  · exact (ModuleCat.epi_iff_surjective _).mpr (parabolicStandardMap_surjective Q Λ θ β hQ g hg)

end ShortExact

end Stendhal

end Categorification
