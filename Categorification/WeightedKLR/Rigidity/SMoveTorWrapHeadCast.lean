/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveTorWrapHead

/-!
# Proposition 7.22 (c) for modules given over equal labels and weights

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c). The S-move pairs a module `L` over the last two red strands with a
module `L'` over the first two. In the library both are constructed over their own red labels
and black weights (the coevaluation labels of Lemma 7.3, the black weight of a divided word),
which agree with the S-move's `Λ ∘ Fin.natAdd 1`, `rightLabels Λ` and common black weight `ν`
only propositionally. `castTensorModule` transports a module along such equalities, and
`SMove.derivedTensorHomology_reflect_wrapHead_rightStd_one_dimensional_of_eq` restates
`SMove.derivedTensorHomology_reflect_wrapHead_rightStd_one_dimensional` with labels, black
weight and word `𝐮` related to the S-move's by equalities, so that the hypotheses can be supplied
in the form in which the library proves them.

## Main definitions

* `Stendhal.castTensorModule`: a module over `T^{Φ'}(ν')` as a module over `T^{Φ}(ν)`, along
  `Φ = Φ'` and `ν = ν'`.

## Main results

* `SMove.derivedTensorHomology_reflect_wrapHead_rightStd_one_dimensional_of_eq`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)

/-- A module over `T^{Φ'}(ν')` as a module over `T^{Φ}(ν)`, along equalities of the red labels
and of the black weights. -/
def castTensorModule {n : ℕ} {Φ Φ' : Fin n → I →₀ ℕ} (hΦ : Φ = Φ') {ν ν' : Multiset I}
    (hν : ν = ν') (M : ModuleCat.{0} (TensorProductAlgebra k Q Φ' ν')) :
    ModuleCat.{0} (TensorProductAlgebra k Q Φ ν) := by
  subst hΦ hν
  exact M

theorem castTensorModule_rfl {n : ℕ} (Φ : Fin n → I →₀ ℕ) (ν : Multiset I)
    (M : ModuleCat.{0} (TensorProductAlgebra k Q Φ ν)) :
    castTensorModule Q (rfl : Φ = Φ) (rfl : ν = ν) M = M :=
  rfl

end Categorification.Stendhal

namespace Categorification.Stendhal.SMove

open CategoryTheory CategoryTheory.Limits Abelian KLR KLRAlgebra Equiv MulOpposite
open BraidedStendhalAlgebra TwoRedErase
open DG DG.DerivedCategory
open scoped DG.DegreeZero

universe w v

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) (Λ : Fin (1 + (1 + 1)) → I →₀ ℕ) (d : List (I × ℕ))
  {Φ Φ' : Fin 2 → I →₀ ℕ} (hX : Λ ∘ Fin.natAdd 1 = Φ) (hY : rightLabels Λ = Φ')
  {ν : Multiset I} (hν : ν = (expandDiv d : Multiset I))

local notation "νᵈ" => (expandDiv d : Multiset I)
local notation "zΦ" => CycKLR.mk k Q (fun i => Polynomial.X ^ Φ 0 i) (expandDiv d : Multiset I)
  (hflip (divIdem (KLRAlgebra.Seq.ofList (expandDiv d) rfl) (blocksDiv d 0)))
local notation "Λ₃" => (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1) : Fin (1 + 1 + 1) → I →₀ ℕ)

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight (1 + 1 + 1) ν))) → List ℕ}
    (hρ : TypeA.IsReducedChoice ρ)

variable [HasDerivedCategory.{w, 0}
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (ν := ν)
      (List.map (1 : Perm (Fin (1 + 1 + 1))) (List.finRange (1 + 1 + 1))))]
  [HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν)]
  [HasDerivedCategory.{w, 0} ℤ]
  [HasExt.{v} (ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) ν))]
  [HasExt.{v} (ModuleCat.{0} (TensorProductAlgebra k Q Φ' ν))]

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

include hρ hX hY hν in
/-- **Proposition 7.22 (c) with the head of the wrap projective on the left, along equalities of
labels and weights** (Webster, arXiv:1309.3796v3, §7.3, Proposition 7.22, gap (c) of its
proof). This is `derivedTensorHomology_reflect_wrapHead_rightStd_one_dimensional`, with `L` the
head of the wrap projective of `d` over labels `Φ = Λ ∘ Fin.natAdd 1` and black weight
`d̂ = ν`, with `L'` over labels `Φ' = rightLabels Λ` and with the word `𝐮 = d̂.reverse` of its
second clause of Proposition 7.8; the modules are transported to the S-move by
`castTensorModule`. The hypotheses are those of
`derivedTensorHomology_reflect_wrapHead_rightStd_one_dimensional` (Rouquier `Q` the only route
hypothesis). -/
theorem derivedTensorHomology_reflect_wrapHead_rightStd_one_dimensional_of_eq
    {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
    (hRX : LastDotRelation Q Φ νᵈ) (hne : zΦ ≠ 0)
    (hgen : ∀ y : CycKLR k Q (fun i => Polynomial.X ^ Φ 0 i) νᵈ, zΦ * y = y → y ≠ 0 →
      ∃ c, y * c = zΦ)
    (hscalar : ∀ x : CycKLR k Q (fun i => Polynomial.X ^ Φ 0 i) νᵈ, zΦ * x * zΦ = x →
      ∃ c : k, x = c • zΦ)
    (L' : ModuleCat.{0} (TensorProductAlgebra k Q Φ' ν))
    [FiniteDimensional k L']
    (hL' : ∀ (s : Seq (stendhalWeight (1 + 1) ν)) (hs : IsRedOrdered s), ¬HasLastRed s →
      ∀ x : L', loadingIdem Q Φ' s hs • x = 0)
    (u : List I) (hu : u = (expandDiv d).reverse)
    (h₀ : 0 + wordWt u 0 = ν) (t : Seq (stendhalWeight 1 0))
    (ht : IsRedOrdered t)
    (het : TensorProductAlgebra.mk Q (Φ' ∘ Fin.castSucc) 0 (StendhalAlgebra.e t ht) = 1)
    (Y₀ : ModuleCat.{0} (CycKLR k Q (fun j => Polynomial.X ^ Φ' (Fin.last 1) j) (wordWt u 0)))
    (hss : ∀ (M : Type) [AddCommGroup M]
      [Module (CycKLR k Q (fun j => Polynomial.X ^ Φ' (Fin.last 1) j) (wordWt u 0)) M]
      [Module.Finite (CycKLR k Q (fun j => Polynomial.X ^ Φ' (Fin.last 1) j) (wordWt u 0)) M],
      ∃ n : ℕ, Nonempty (M ≃ₗ[CycKLR k Q (fun j => Polynomial.X ^ Φ' (Fin.last 1) j)
        (wordWt u 0)] (Fin n → Y₀)))
    {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (ι : J → (Y₀ →ₗ[CycKLR k Q (fun j => Polynomial.X ^ Φ' (Fin.last 1) j) (wordWt u 0)]
      cycWord Q Φ' u))
    (π : J → (cycWord Q Φ' u →ₗ[CycKLR k Q (fun j => Polynomial.X ^ Φ' (Fin.last 1) j)
      (wordWt u 0)] Y₀))
    (hιπ : ∀ i j, (π j).comp (ι i) = if i = j then LinearMap.id else 0)
    (htot : ∑ j, (ι j).comp (π j) = LinearMap.id)
    (htop : Module.finrank k (Ext.{v}
      (tensorStd Q Φ' hQ h₀ (oldProj Q Φ' 0 t ht) Y₀) L' (Multiset.card ν)) = 1)
    (hJ : Fintype.card J = (d.map fun q => q.2.factorial).prod) :
    Nonempty ((homologyFunctor (A := ℤ) ℤ (-(Multiset.card ν : ℤ))).obj
        ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q Λ₃ ν)
          ((reflectOne Q Λ₃ hQ hρ).obj ((leftStd Q hQ Λ ν).obj
            (castTensorModule Q hX hν (flipLeft Q Φ νᵈ (rIdeal (wrapIdem Q Φ νᵈ zΦ) ⧸
              coevaluationTrace (cutIdem Q Φ νᵈ))))))).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
            ((rightStd Q hQ Λ₃ ν).obj (castTensorModule Q hY rfl L'))))) ≃+ k) ∧
      ∀ n : ℤ, n ≠ -(Multiset.card ν : ℤ) → IsZero ((homologyFunctor (A := ℤ) ℤ n).obj
        ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q Λ₃ ν)
          ((reflectOne Q Λ₃ hQ hρ).obj ((leftStd Q hQ Λ ν).obj
            (castTensorModule Q hX hν (flipLeft Q Φ νᵈ (rIdeal (wrapIdem Q Φ νᵈ zΦ) ⧸
              coevaluationTrace (cutIdem Q Φ νᵈ))))))).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
            ((rightStd Q hQ Λ₃ ν).obj (castTensorModule Q hY rfl L')))))) := by
  subst hX hY hν hu
  exact derivedTensorHomology_reflect_wrapHead_rightStd_one_dimensional.{w, v} Q hQ Λ d hρ hR
    hRX hne hgen hscalar L' hL' h₀ t ht het Y₀ hss ι π hιπ htot htop hJ

end Categorification.Stendhal.SMove
