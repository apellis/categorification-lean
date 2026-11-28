/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CutSpectTensorRepresented
import Categorification.Algebra.TensorRepresentedIso

/-!
# The standardization in stages is tensoring with a bimodule

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1: the
standardization with singleton blocks, built in stages from partial standardizations at cuts
(`singStd`), is tensoring with its value on the regular module
(`isTensorRepresented_singStd`). Each stage is a restriction of scalars along an associator
or a partial standardization at a cut, and both are represented by tensoring
(`isTensorRepresented_restrictScalars`, `isTensorRepresented_cutSpectFunctor`).

## Main results

* `Stendhal.isTensorRepresented_singStd`: the standardization in stages is represented by
  tensoring.
-/

universe u

noncomputable section

namespace Categorification

open CategoryTheory TensorRepresented

/-- The identity functor is represented by tensoring with the regular bimodule. -/
theorem isTensorRepresented_id {B : Type u} [Ring B] :
    IsTensorRepresented (𝟭 (ModuleCat.{u} B)) :=
  IsTensorRepresented.of_iso (ModuleCat.restrictScalarsId' (RingHom.id B) rfl)
    (isTensorRepresented_restrictScalars (RingHom.id B))

/-- Tensor representability transported along an equality of functors. -/
theorem isTensorRepresented_of_eq {A B : Type u} [Ring A] [Ring B]
    {F G : ModuleCat.{u} B ⥤ ModuleCat.{u} A} [G.Additive] (h : G = F) (hFa : F.Additive)
    (hF : IsTensorRepresented F) : IsTensorRepresented G := by
  subst h
  exact hF

/-- `IsTensorRepresented.comp`, with the additivity of the factors given explicitly. -/
theorem isTensorRepresented_comp {A B C : Type u} [Ring A] [Ring B] [Ring C]
    {F : ModuleCat.{u} B ⥤ ModuleCat.{u} A} {G : ModuleCat.{u} A ⥤ ModuleCat.{u} C}
    (iF : F.Additive) (iG : G.Additive) (hF : IsTensorRepresented F)
    (hG : IsTensorRepresented G) :
    @IsTensorRepresented _ _ _ _ (F ⋙ G) (Stendhal.additive_comp' iF iG) :=
  IsTensorRepresented.comp F G hF hG

namespace Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

variable {I k : Type u} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q)

/-- **The standardization in stages is tensoring with a bimodule**: the standardization with
singleton blocks and a spectator `E` is represented by tensoring with its value on the
regular module (Webster, arXiv:1309.3796v3, §5.1). -/
theorem isTensorRepresented_singStd : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) →
    (θ : Fin n → Multiset I) → (E : AlgCat.{u} k) →
    IsTensorRepresented (singStd Q hQ n Λ θ E)
  | 0, _, _, _ => isTensorRepresented_id
  | n + 1, Λ, θ, E => by
    refine isTensorRepresented_of_eq (singStd.eq_2 Q hQ E n Λ θ) ?a ?b
    case b =>
      exact isTensorRepresented_comp _ _ (isTensorRepresented_restrictScalars _)
        (isTensorRepresented_comp (singStd_additive Q hQ n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
            (AlgCat.of k (singLast Q Λ θ ⊗[k] E))) _
          (isTensorRepresented_singStd n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
            (AlgCat.of k (singLast Q Λ θ ⊗[k] E)))
          (isTensorRepresented_comp _ (cutSpectFunctor_additive (a := n) (r := 1) Q Λ
              (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n)) E hQ)
            (isTensorRepresented_restrictScalars _)
            (isTensorRepresented_cutSpectFunctor _ _ _ _ _ hQ)))

end Stendhal

end Categorification
