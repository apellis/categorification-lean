/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutWindowResSum
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KPsiFlip

/-!
# The target of (T) is the corner of the cut loading

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5.

The red-ordered idempotent of the window is the unit of `T^{Λc}(ν₀)`
(`tensorOfKLR_redOrderedKLR`), and the unit of the middle block acts on `Res X` as the identity
(`plusMidEnd_one`). So the target `e_red · e(l) · 𝕊Lay^c` of (T)
(`windowRedOrderedCornerEquiv`) is the corner `e(l) · 𝕊Lay^c` of the cut loading in the layer
`0` of `S_cut(Res X)` (`cutWindowCorner_redOrdered`).

Webster's proof does not spell this out. No new hypothesis.

## Main results

* `Stendhal.cutStandardLayerMap_id`, `Stendhal.CupCap.plusMidEnd_one`,
  `Stendhal.CupCap.cutWindowCorner_one`, `Stendhal.CupCap.cutWindowCorner_redOrdered`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra

section Generic

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (a + r) → I →₀ ℕ} {θ β : Multiset I}
  {N : Type*} [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N]

/-- The identity acts as the identity on the layers of `𝕊(N)`. -/
theorem cutStandardLayerMap_id (n c : ℕ) :
    cutStandardLayerMap (LinearMap.id : N →ₗ[cutFactorAlgebra Q Λ θ β] N) n c = LinearMap.id :=
  Submodule.linearMap_qext _ (LinearMap.ext fun v =>
    (cutStandardLayerMap_mk _ n c v).trans (congrArg Submodule.Quotient.mk (Subtype.ext
      (LinearMap.congr_fun (cutStandardMap_id (Q := Q) (Λ := Λ) (θ := θ) (β := β)
        (N := N)) v.1))))

end Generic

namespace CupCap

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I}

variable (X : Type) [AddCommGroup X] [Module k X]
  [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] (hQ : KLRSymm Q)

omit [Module k X] [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] in
/-- The unit of the middle block acts on `Res X` as the identity. -/
theorem plusMidEnd_one :
    plusMidEnd (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (θ := θ) (γ := γ) (ν₀ := ν₀)
      X 1 = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  change (((1 : TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) θ) ⊗ₜ
      ((1 : TensorProductAlgebra k Q Λc ν₀) ⊗ₜ
        (1 : TensorProductAlgebra k Q (plusTailLabels Λ j hj) γ)) :
      PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) • (show X from x) : X) = x
  rw [← Algebra.TensorProduct.one_def, ← Algebra.TensorProduct.one_def]
  exact one_smul _ (show X from x)

variable (s : Seq (stendhalWeight ℓ (θ + γ)))

/-- `1 · e(l)` is the corner of the cut loading. -/
theorem cutWindowCorner_one :
    cutWindowCorner Λ Λc (Q := Q) (j := j) (hj := hj) (θ := θ) (γ := γ) (ν₀ := ν₀) X hQ s 1 =
      cutLayerAct (Λ := cutLabels j hj Λ) hQ (N := PlusRes j hj Q Λ Λc θ γ ν₀ X)
        (preservesMackeyFilt_e (Q := stendhalQ Q (cutLabels j hj Λ)) (n := midPos j s)
          (n'' := Multiset.card
            (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ)))
          (cutLoading j hj θ γ s)) 0 := by
  have h1 := plusMidEnd_one (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (θ := θ)
    (γ := γ) (ν₀ := ν₀) X
  have h2 := cutStandardLayerMap_id (Q := Q) (Λ := cutLabels j hj Λ) (θ := θ) (β := γ)
    (N := PlusRes j hj Q Λ Λc θ γ ν₀ X) (midPos j s) 0
  exact (congrArg (fun g => cutStandardLayerMap g (midPos j s) 0 ∘ₗ
      cutLayerAct (Λ := cutLabels j hj Λ) hQ (N := PlusRes j hj Q Λ Λc θ γ ν₀ X)
        (preservesMackeyFilt_e (Q := stendhalQ Q (cutLabels j hj Λ)) (n := midPos j s)
          (n'' := Multiset.card
            (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ)))
          (cutLoading j hj θ γ s)) 0) h1).trans
    ((congrArg (· ∘ₗ cutLayerAct (Λ := cutLabels j hj Λ) hQ (N := PlusRes j hj Q Λ Λc θ γ ν₀ X)
        (preservesMackeyFilt_e (Q := stendhalQ Q (cutLabels j hj Λ)) (n := midPos j s)
          (n'' := Multiset.card
            (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ)))
          (cutLoading j hj θ γ s)) 0) h2).trans (LinearMap.id_comp _))

/-- **The target of (T)**: `e_red · e(l) = e(l)` on the layer `0` of `S_cut(Res X)`. -/
theorem cutWindowCorner_redOrdered :
    cutWindowCorner Λ Λc (Q := Q) (j := j) (hj := hj) (θ := θ) (γ := γ) (ν₀ := ν₀) X hQ s
        (tensorOfKLR Q Λc ν₀ (redOrderedKLR k Q Λc ν₀)) =
      cutLayerAct (Λ := cutLabels j hj Λ) hQ (N := PlusRes j hj Q Λ Λc θ γ ν₀ X)
        (preservesMackeyFilt_e (Q := stendhalQ Q (cutLabels j hj Λ)) (n := midPos j s)
          (n'' := Multiset.card
            (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ)))
          (cutLoading j hj θ γ s)) 0 :=
  (congrArg (cutWindowCorner Λ Λc (Q := Q) (j := j) (hj := hj) (θ := θ) (γ := γ) (ν₀ := ν₀)
    X hQ s) (tensorOfKLR_redOrderedKLR Λc ν₀)).trans (cutWindowCorner_one X hQ s)

end CupCap

end Categorification.Stendhal
