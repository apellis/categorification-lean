/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSpectatorChange

/-!
# Naturality of the changes of spectator

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1 (the
partial standardization functors after Definition 5.4), toward the derived form of
Lemma 7.19 (K). The partial standardization at a cut is functorial (`cutStandardMap`), so a
commutative square of input maps gives a commutative square of standardizations
(`cutStandardMap_square`). Hence the partial standardization of a change of spectator is
natural (`cutSpectStandardEquivOf_natural`), and so is the standardization in stages of a
change of spectator (`singStdSpectatorEquiv_natural`).

## Main results

* `Stendhal.cutStandardMap_square`: functoriality on commutative squares.
* `Stendhal.cutSpectStandardEquivOf_natural`: naturality of `cutSpectStandardEquivOf`.
* `Stendhal.singStdSpectatorEquiv_natural`: naturality of `singStdSpectatorEquiv`.
-/

set_option backward.isDefEq.respectTransparency false

universe u

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra TypeA
open scoped TensorProduct

section Cut

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)

variable {N₁ N₂ N₃ N₄ : Type*}
  [AddCommGroup N₁] [Module k N₁] [Module (cutFactorAlgebra Q Λ θ β) N₁]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N₁]
  [AddCommGroup N₂] [Module k N₂] [Module (cutFactorAlgebra Q Λ θ β) N₂]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N₂]
  [AddCommGroup N₃] [Module k N₃] [Module (cutFactorAlgebra Q Λ θ β) N₃]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N₃]
  [AddCommGroup N₄] [Module k N₄] [Module (cutFactorAlgebra Q Λ θ β) N₄]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N₄]

/-- **The partial standardization at a cut on a commutative square.** -/
theorem cutStandardMap_square (f : N₁ →ₗ[cutFactorAlgebra Q Λ θ β] N₂)
    (g : N₂ →ₗ[cutFactorAlgebra Q Λ θ β] N₄) (f' : N₁ →ₗ[cutFactorAlgebra Q Λ θ β] N₃)
    (g' : N₃ →ₗ[cutFactorAlgebra Q Λ θ β] N₄) (h : ∀ n, g (f n) = g' (f' n))
    (z : CutStandard Q Λ θ β N₁) :
    cutStandardMap Q Λ θ β g (cutStandardMap Q Λ θ β f z) =
      cutStandardMap Q Λ θ β g' (cutStandardMap Q Λ θ β f' z) :=
  (cutStandardMap_comp Q Λ θ β f g z).symm.trans
    ((congrArg (fun F => cutStandardMap Q Λ θ β F z) (LinearMap.ext h)).trans
      (cutStandardMap_comp Q Λ θ β f' g' z))

variable {E E' : Type*} [Ring E] [Algebra k E] [Ring E'] [Algebra k E'] (φ : E →ₐ[k] E')

variable {N M : Type*} [AddCommGroup N] [Module k N] [Module (cutSpectAlgebra Q Λ θ β E) N]
  [IsScalarTower k (cutSpectAlgebra Q Λ θ β E) N]
  [AddCommGroup M] [Module k M] [Module (cutSpectAlgebra Q Λ θ β E) M]
  [IsScalarTower k (cutSpectAlgebra Q Λ θ β E) M]
  {N' M' : Type*} [AddCommGroup N'] [Module k N'] [Module (cutSpectAlgebra Q Λ θ β E') N']
  [IsScalarTower k (cutSpectAlgebra Q Λ θ β E') N']
  [AddCommGroup M'] [Module k M'] [Module (cutSpectAlgebra Q Λ θ β E') M']
  [IsScalarTower k (cutSpectAlgebra Q Λ θ β E') M']
  (f : N ≃+ N') (hf : ∀ (x : cutSpectAlgebra Q Λ θ β E) (n : N),
    f (x • n) = cutSpectMapAlg Q Λ θ β φ x • f n)
  (f₂ : M ≃+ M') (hf₂ : ∀ (x : cutSpectAlgebra Q Λ θ β E) (n : M),
    f₂ (x • n) = cutSpectMapAlg Q Λ θ β φ x • f₂ n)
  (hQ : KLRSymm Q)

/-- **The partial standardization of a change of spectator is natural.** -/
theorem cutSpectStandardEquivOf_natural (g : N →ₗ[cutSpectAlgebra Q Λ θ β E] M)
    (g' : N' →ₗ[cutSpectAlgebra Q Λ θ β E'] M') (h : ∀ n, f₂ (g n) = g' (f n))
    (z : CutSpectStandard Q Λ θ β E N hQ) :
    cutSpectStandardEquivOf Q Λ θ β φ f₂ hf₂ hQ (cutSpectStandardMap Q Λ θ β hQ g z) =
      cutSpectStandardMap Q Λ θ β hQ g' (cutSpectStandardEquivOf Q Λ θ β φ f hf hQ z) :=
  cutStandardMap_square Q Λ θ β _ _ _ _ h z

end Cut

section Singletons

variable {I k : Type u} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q)

/-- The input of the first stage, as a functor. -/
abbrev singInFunctor (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (E : AlgCat.{u} k) :
    ModuleCat.{u} (singAlg Q (n + 1) Λ θ ⊗[k] E) ⥤
    ModuleCat.{u} (singAlg Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) ⊗[k]
      (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k)) :=
  ModuleCat.restrictScalars.{u} (singAssocIn Q n Λ θ E)

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

/-- **The standardization in stages of a change of spectator is natural**: for changes of
spectator `F : Z ≅ Z'` and `G : W ≅ W'` and maps `g : Z → W`, `g' : Z' → W'` with
`G ∘ g = g' ∘ F`, the standardizations in stages form a commutative square. -/
theorem singStdSpectatorEquiv_natural : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) →
    (θ : Fin n → Multiset I) → {E E' : AlgCat.{u} k} → (φ : E →ₐ[k] E') →
    {Z W : ModuleCat.{u} (singAlg Q n Λ θ ⊗[k] E)} →
    {Z' W' : ModuleCat.{u} (singAlg Q n Λ θ ⊗[k] E')} →
    (F : SpectatorEquiv (singAlg Q n Λ θ) φ Z Z') →
    (G : SpectatorEquiv (singAlg Q n Λ θ) φ W W') → (g : Z ⟶ W) → (g' : Z' ⟶ W') →
    (∀ z, G.equiv (g.hom z) = g'.hom (F.equiv z)) →
    ∀ x, (singStdSpectatorEquiv Q hQ n Λ θ φ G).equiv ((singStd Q hQ n Λ θ E).map g |>.hom x) =
      ((singStd Q hQ n Λ θ E').map g').hom ((singStdSpectatorEquiv Q hQ n Λ θ φ F).equiv x)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, h => h
  | n + 1, Λ, θ, E, E', φ, Z, W, Z', W', F, G, g, g', h => fun x => by
    have ih := singStdSpectatorEquiv_natural n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
        (singLastMap Q Λ θ φ) (SpectatorEquiv.singIn Q F) (SpectatorEquiv.singIn Q G)
        ((singInFunctor Q n Λ θ E).map g) ((singInFunctor Q n Λ θ E').map g') h
    exact cutStandardMap_square _ _ _ _ _ _ _ _ ih x

end Singletons

end Categorification.Stendhal
