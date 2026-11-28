/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSpectatorTensorStages
import Categorification.WeightedKLR.RedStrands.PartialStandardizationNatural

/-!
# Naturality of the standardization in stages of a tensor isomorphism

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1 and §7.3
(the computation of `S_+(Z ⊠ L)` in the proof of Lemma 7.19), toward the derived form of
Lemma 7.19 (K). For tensor isomorphisms `F : M ⊗ L ≅ P` and `G : W ⊗ L ≅ P'` and maps
`g : M → W`, `g' : P → P'` with `G ∘ (g ⊗ L) = g' ∘ F` on pure tensors, the standardizations in
stages form a commutative square (`singStdTensorEquiv_natural`).

## Main results

* `Stendhal.cutStandardMap_square3`: functoriality on a square of composites of three maps.
* `Stendhal.singOut_natural`: naturality of the last stage.
* `Stendhal.singStdTensorEquiv_natural`: naturality of `singStdTensorEquiv`.
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

variable {N₁ N₂ N₃ N₄ N₅ N₆ : Type*}
  [AddCommGroup N₁] [Module k N₁] [Module (cutFactorAlgebra Q Λ θ β) N₁]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N₁]
  [AddCommGroup N₂] [Module k N₂] [Module (cutFactorAlgebra Q Λ θ β) N₂]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N₂]
  [AddCommGroup N₃] [Module k N₃] [Module (cutFactorAlgebra Q Λ θ β) N₃]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N₃]
  [AddCommGroup N₄] [Module k N₄] [Module (cutFactorAlgebra Q Λ θ β) N₄]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N₄]
  [AddCommGroup N₅] [Module k N₅] [Module (cutFactorAlgebra Q Λ θ β) N₅]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N₅]
  [AddCommGroup N₆] [Module k N₆] [Module (cutFactorAlgebra Q Λ θ β) N₆]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N₆]

/-- **The partial standardization at a cut on a square of composites of three maps.** -/
theorem cutStandardMap_square3 (c : N₁ →ₗ[cutFactorAlgebra Q Λ θ β] N₂)
    (b : N₂ →ₗ[cutFactorAlgebra Q Λ θ β] N₃) (a' : N₃ →ₗ[cutFactorAlgebra Q Λ θ β] N₄)
    (f : N₁ →ₗ[cutFactorAlgebra Q Λ θ β] N₅) (e : N₅ →ₗ[cutFactorAlgebra Q Λ θ β] N₆)
    (d : N₆ →ₗ[cutFactorAlgebra Q Λ θ β] N₄) (h : ∀ n, a' (b (c n)) = d (e (f n)))
    (z : CutStandard Q Λ θ β N₁) :
    cutStandardMap Q Λ θ β a' (cutStandardMap Q Λ θ β b (cutStandardMap Q Λ θ β c z)) =
      cutStandardMap Q Λ θ β d (cutStandardMap Q Λ θ β e (cutStandardMap Q Λ θ β f z)) :=
  (congrArg (cutStandardMap Q Λ θ β a') (cutStandardMap_comp Q Λ θ β c b z).symm).trans
    ((cutStandardMap_square Q Λ θ β (b ∘ₗ c) a' (e ∘ₗ f) d h z).trans
      (congrArg (cutStandardMap Q Λ θ β d) (cutStandardMap_comp Q Λ θ β f e z)))

end Cut

section Singletons

variable {I k : Type u} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q)

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {B : AlgCat.{u} k} {L : Type u} [AddCommGroup L] [Module k L] [Module B L]

/-- The input of the last stage, as a functor. -/
abbrev singOutFunctor (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (E : AlgCat.{u} k) :
    ModuleCat.{u} (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
      (singWeight n (θ ∘ Fin.castSucc)) ⊗[k]
        (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k)) ⥤
    ModuleCat.{u} (cutSpectAlgebra (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
      (θ (Fin.last n)) E) :=
  ModuleCat.restrictScalars.{u} (singAssocOut Q n Λ θ E)

variable {C E : AlgCat.{u} k} {n : ℕ} {Λ : Fin (n + 1) → I →₀ ℕ} {θ : Fin (n + 1) → Multiset I}
  {ψ : C ⊗[k] B →ₐ[k] E}
  {Y W : ModuleCat.{u} (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
    (singWeight n (θ ∘ Fin.castSucc)) ⊗[k] (AlgCat.of k (singLast Q Λ θ ⊗[k] C) : AlgCat.{u} k))}
  {Y' W' : ModuleCat.{u} (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
    (singWeight n (θ ∘ Fin.castSucc)) ⊗[k] (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k))}

/-- The last stage on pure tensors. -/
theorem singOut_equiv_tmul
    (G : TensorSpectatorEquiv (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
      (singWeight n (θ ∘ Fin.castSucc))) (AlgCat.of k (singLast Q Λ θ ⊗[k] C) : AlgCat.{u} k) B
      (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k) (singTensorMap Q Λ θ ψ) Y L Y')
    (x : (cutSpectFunctor (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
      (θ (Fin.last n)) C hQ).obj (singOutObj Q n Λ θ C Y)) (v : L) :
    (G.singOut Q hQ).equiv (x ⊗ₜ[k] v) =
      cutSpectStandardEquivOf (a := n) (r := 1) Q Λ _ _ ψ (N := singOutTensorObj Q Λ θ ψ Y')
        (N' := singOutObj Q n Λ θ E Y') (AddEquiv.refl _) (fun _ _ => rfl) hQ
        (cutStandardMap (a := n) (r := 1) Q Λ _ _
          (cutSpectTensorSlice (a := n) (r := 1) Q Λ _ _ (singOutTensorEquiv Q G)
            (isCutSpectTensor_singOutTensorEquiv Q G) v) x) := rfl

/-- **The last stage is natural**, given the naturality of the tensor isomorphism on its
input. -/
theorem singOut_natural
    (G : TensorSpectatorEquiv (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
      (singWeight n (θ ∘ Fin.castSucc))) (AlgCat.of k (singLast Q Λ θ ⊗[k] C) : AlgCat.{u} k) B
      (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k) (singTensorMap Q Λ θ ψ) Y L Y')
    (G' : TensorSpectatorEquiv (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
      (singWeight n (θ ∘ Fin.castSucc))) (AlgCat.of k (singLast Q Λ θ ⊗[k] C) : AlgCat.{u} k) B
      (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k) (singTensorMap Q Λ θ ψ) W L W')
    (g : Y ⟶ W) (g' : Y' ⟶ W')
    (h : ∀ m v, G'.equiv (g.hom m ⊗ₜ[k] v) = g'.hom (G.equiv (m ⊗ₜ[k] v)))
    (x : (cutSpectFunctor (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
      (θ (Fin.last n)) C hQ).obj (singOutObj Q n Λ θ C Y)) (v : L) :
    (G'.singOut Q hQ).equiv (((cutSpectFunctor (a := n) (r := 1) Q Λ
        (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n)) C hQ).map
          ((singOutFunctor Q n Λ θ C).map g)).hom x ⊗ₜ[k] v) =
      ((cutSpectFunctor (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
        (θ (Fin.last n)) E hQ).map ((singOutFunctor Q n Λ θ E).map g')).hom
        ((G.singOut Q hQ).equiv (x ⊗ₜ[k] v)) := by
  have hsq := cutStandardMap_square3 (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
    (θ (Fin.last n))
    (cutSpectInputHom (a := n) (r := 1) Q Λ _ _ ((singOutFunctor Q n Λ θ C).map g).hom)
    (cutSpectTensorSlice (a := n) (r := 1) Q Λ _ _ (singOutTensorEquiv Q G')
      (isCutSpectTensor_singOutTensorEquiv Q G') v)
    (cutSpectInputEquivOf (a := n) (r := 1) Q Λ _ _ ψ (N := singOutTensorObj Q Λ θ ψ W')
      (N' := singOutObj Q n Λ θ E W') (AddEquiv.refl _) (fun _ _ => rfl)).toLinearMap
    (cutSpectTensorSlice (a := n) (r := 1) Q Λ _ _ (singOutTensorEquiv Q G)
      (isCutSpectTensor_singOutTensorEquiv Q G) v)
    (cutSpectInputEquivOf (a := n) (r := 1) Q Λ _ _ ψ (N := singOutTensorObj Q Λ θ ψ Y')
      (N' := singOutObj Q n Λ θ E Y') (AddEquiv.refl _) (fun _ _ => rfl)).toLinearMap
    (cutSpectInputHom (a := n) (r := 1) Q Λ _ _ ((singOutFunctor Q n Λ θ E).map g').hom)
    (fun m => h m v) x
  exact hsq

/-- **The standardization in stages of a tensor isomorphism is natural**: for tensor
isomorphisms `F : M ⊗ L ≅ P`, `G : W ⊗ L ≅ P'` and maps `g : M → W`, `g' : P → P'` with
`G ∘ (g ⊗ L) = g' ∘ F` on pure tensors, `singStdTensorEquiv` intertwines the standardizations
of `g` and `g'`. -/
theorem singStdTensorEquiv_natural : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) →
    (θ : Fin n → Multiset I) → {C E : AlgCat.{u} k} → (ψ : C ⊗[k] B →ₐ[k] E) →
    {M W : ModuleCat.{u} (singAlg Q n Λ θ ⊗[k] C)} →
    {P P' : ModuleCat.{u} (singAlg Q n Λ θ ⊗[k] E)} →
    (F : TensorSpectatorEquiv (singAlg Q n Λ θ) C B E ψ M L P) →
    (G : TensorSpectatorEquiv (singAlg Q n Λ θ) C B E ψ W L P') → (g : M ⟶ W) →
    (g' : P ⟶ P') → (∀ m v, G.equiv (g.hom m ⊗ₜ[k] v) = g'.hom (F.equiv (m ⊗ₜ[k] v))) →
    ∀ (x : (singStd Q hQ n Λ θ C).obj M) (v : L),
      (singStdTensorEquiv Q hQ n Λ θ ψ G).equiv (((singStd Q hQ n Λ θ C).map g).hom x ⊗ₜ[k] v) =
        ((singStd Q hQ n Λ θ E).map g').hom ((singStdTensorEquiv Q hQ n Λ θ ψ F).equiv
          (x ⊗ₜ[k] v))
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, h => h
  | n + 1, Λ, θ, C, E, ψ, _, _, _, _, F, G, g, g', h => fun x v =>
    singOut_natural Q hQ (singStdTensorEquiv Q hQ n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
      (singTensorMap Q Λ θ ψ) (TensorSpectatorEquiv.singIn Q F))
      (singStdTensorEquiv Q hQ n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
      (singTensorMap Q Λ θ ψ) (TensorSpectatorEquiv.singIn Q G))
      ((singStd Q hQ n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) _).map
        ((singInFunctor Q n Λ θ C).map g))
      ((singStd Q hQ n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) _).map
        ((singInFunctor Q n Λ θ E).map g'))
      (singStdTensorEquiv_natural n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
        (singTensorMap Q Λ θ ψ) (TensorSpectatorEquiv.singIn Q F)
        (TensorSpectatorEquiv.singIn Q G) ((singInFunctor Q n Λ θ C).map g)
        ((singInFunctor Q n Λ θ E).map g') h) x v

end Singletons

end Categorification.Stendhal
