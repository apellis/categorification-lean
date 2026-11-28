/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveDiagonalHigherTor
import Categorification.WeightedKLR.Rigidity.SMoveDiagonalTorZero
import Categorification.WeightedKLR.Rigidity.SMoveInnerRedSeparation
import Categorification.WeightedKLR.RedStrands.OrderedStandardResolution

/-!
# The S-move Tor lemmas for Rouquier parameters

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c). The Tor lemmas of the S-move carry two route hypotheses: the
ordered standard covers `DC` of the left standards (input of the Lemma 6.12 Tor vanishing) and
the standard filtrations `hold` of the projectives of the first red strands (Proposition 5.20).
For a Rouquier choice of `Q` both are library theorems: `DC` is `orderedStandardCovers` built
from `exists_hasFiltration_leftUpper_of_rouquier` (Corollary 5.21), and `hold` is
`hasStandardFiltrations_of_rouquier` (Proposition 5.20). This file discharges them, and states
the diagonal term over the coefficient ring `ℤ` of the other Tor lemmas: `Tor₀^ℤ(M^r, M)` is
additively a copy of `k`, using the `k`-dimension count of
`finrank_tensorProductOver_reflectOne_last`.

## Main results

* `rouquierStandardCovers`: the ordered standard covers of the left standards, for Rouquier `Q`.
* `torAcyclic_reflect_stdLayer_of_ne_of_rouquier`: off-diagonal vanishing at the last red strand.
* `SMove.torAcyclic_reflect_leftStd_rightStd_of_ne_of_rouquier`: off-diagonal vanishing at the
  middle red strand.
* `isZero_derivedTensorHomology_reflectOne_last_of_ne_zero`: no higher Tor on the diagonal.
* `nonempty_addEquiv_derivedTensorHomology_int_reflectOne_last`: `Tor₀^ℤ(M^r, M) ≃+ k`.
* `torConcentrated_reflectOne_last`: both, in one statement over `ℤ`.

The remaining hypotheses are those of Proposition 7.8 (`exists_stdResolution_last`), and a
Rouquier choice of `Q`.
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits Abelian KLR ModuleFiltration Equiv BraidedStendhalAlgebra
open DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

universe w v

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

/-! ### The route hypotheses for Rouquier parameters -/

section Route

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q) (hQ : KLRSymm Q)

/-- **The ordered standard covers of the left standards** for a Rouquier choice of `Q`
(Webster, arXiv:1309.3796v2, Corollary 5.21, through `orderedStandardCovers`): the datum `DC`
of the S-move Tor lemmas of arXiv:1309.3796v3, Proposition 7.22. -/
def rouquierStandardCovers {n : ℕ} (Λ : Fin n → I →₀ ℕ) (ν : Multiset I) :
    OrderedStandardCovers
      (fun s : {s : Seq (stendhalWeight n ν) // IsRedOrdered s} =>
        ModuleCat.of (TensorProductAlgebra k Q Λ ν) (leftStandard Q Λ s.1 s.2))
      (fun s => seqIdem Q Λ s.1 s.2) (fun s t => StendhalLT s.1 t.1) :=
  orderedStandardCovers Q Λ fun s => by
    exact exists_hasFiltration_leftUpper Q hQ hR
      (fun _ _ => by convert allFiniteDeltaInjective_of_rouquier hR hQ) Λ ν s.1 s.2

include hR hQ in
/-- `HasStandardFiltrations` for a Rouquier choice of `Q` (Webster, arXiv:1309.3796v2,
Proposition 5.20), at the decidable-equality instance in context: the datum `hold` of the
S-move Tor lemmas. -/
theorem hasStandardFiltrations_of_rouquier' {n : ℕ} (Λ : Fin n → I →₀ ℕ) :
    HasStandardFiltrations Q Λ := by
  convert hasStandardFiltrations_of_rouquier hR hQ Λ

end Route

/-! ### The off-diagonal terms -/

section LastRed

variable {I : Type} [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q) {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ)
  [HasDerivedCategory.{w, 0}
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) (List.map (1 : Perm (Fin (ℓ + 1)))
      (List.finRange (ℓ + 1))))]
  [HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q Λ ν)] [HasDerivedCategory.{w, 0} ℤ]

include hρ in
/-- **Off-diagonal Tor vanishing at the last red strand, Rouquier form** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22): for splits `θ + β = θ' + β' = ν` with
`θ ≠ θ'` and finite-dimensional `M`, `M'` over the factor algebras,
`Tor_*^ℤ(S(M)^r, S(M')) = 0`. This is `torAcyclic_reflect_stdLayer_of_ne` with its route
hypotheses `DC` and `hold` discharged. -/
theorem torAcyclic_reflect_stdLayer_of_ne_of_rouquier {C : QuantumGroup.CartanDatum I}
    (hR : IsRouquierQ C Q) {θ β θ' β' : Multiset I} (h : θ + β = ν) (h' : θ' + β' = ν)
    (hne : θ ≠ θ') (M : FactorModule Q Λ θ β) [FiniteDimensional k M.carrier]
    (M' : FactorModule Q Λ θ' β') [FiniteDimensional k M'.carrier] :
    TorAcyclic.{w} (k := ℤ) ((reflectOne Q Λ hQ hρ).obj (stdLayerModule Q Λ hQ ⟨θ, β, h, M⟩))
      (stdLayerModule Q Λ hQ ⟨θ', β', h', M'⟩) :=
  torAcyclic_reflect_stdLayer_of_ne Q Λ hQ hρ hR (rouquierStandardCovers hR hQ Λ ν)
    (hasStandardFiltrations_of_rouquier' hR hQ _) h h' hne M M'

end LastRed

section MiddleRed

namespace SMove

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) (Λ : Fin (1 + (1 + 1)) → I →₀ ℕ) (β₁ : Multiset I)
  {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight (1 + 1 + 1) (β₁ + 0)))) → List ℕ}
  (hρ₂ : TypeA.IsReducedChoice ρ₂)
  [HasDerivedCategory.{w, 0}
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (ν := β₁ + 0)
      (List.map (1 : Perm (Fin (1 + 1 + 1))) (List.finRange (1 + 1 + 1))))]
  [HasDerivedCategory.{w, 0}
    (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (β₁ + 0))]
  [HasDerivedCategory.{w, 0} ℤ]

include hρ₂ in
/-- **Off-diagonal Tor vanishing at the middle red strand, Rouquier form** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22):
`SMove.torAcyclic_reflect_leftStd_rightStd_of_ne` with its route hypotheses `DC` and `hold`
discharged. -/
theorem torAcyclic_reflect_leftStd_rightStd_of_ne_of_rouquier
    {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
    (M : ModuleCat.{0} (cutFactorAlgebra (a := 1) (r := 1) Q (Λ ∘ Fin.natAdd 1) β₁ 0))
    [FiniteDimensional k M]
    {θ' β' : Multiset I} (h' : θ' + β' = β₁ + 0) (hne : θ' ≠ 0)
    (M' : FactorModule Q ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc) θ' β')
    [FiniteDimensional k M'.carrier] :
    TorAcyclic.{w} (k := ℤ) ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ₂).obj
        ((leftStd Q hQ Λ (β₁ + 0)).obj (innerStd Q hQ Λ β₁ 0 M)))
      ((rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (β₁ + 0)).obj
        (stdLayerModule Q ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc) hQ
          ⟨θ', β', h', M'⟩)) :=
  torAcyclic_reflect_leftStd_rightStd_of_ne Q hQ Λ β₁ hρ₂ hR
    (rouquierStandardCovers hR hQ _ _) (hasStandardFiltrations_of_rouquier' hR hQ _) M h' hne M'

end SMove

end MiddleRed

/-! ### The diagonal term over `ℤ` -/

section Diagonal

variable {I : Type} [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q) {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ)
  [HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q Λ ν)] [HasDerivedCategory.{w, 0} ℤ]

include hρ in
/-- **No higher Tor on the diagonal, Rouquier form** (Webster, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22): `isZero_derivedTensorHomology_reflectOne_tensorStd_of_ne_zero` with the
ordered standard covers discharged. For `Y₀` a summand of `R^{λ_ℓ} e(u)` and
`M = S(T^{λ'} e(t) ⊠ Y₀)`, `Tor_n^ℤ(M^r, M) = 0` for `n ≠ 0`. -/
theorem isZero_derivedTensorHomology_reflectOne_last_of_ne_zero
    [HasDerivedCategory.{w, 0}
      (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) (List.map (1 : Perm (Fin (ℓ + 1)))
        (List.finRange (ℓ + 1))))]
    {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
    (u : List I) (h₀ : 0 + wordWt u 0 = ν) (t : Seq (stendhalWeight ℓ 0)) (ht : IsRedOrdered t)
    (Y₀ : ModuleCat.{0} (CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^
      Λ (Fin.last ℓ) j) (wordWt u 0)))
    (ι : Y₀ →ₗ[CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j)
      (wordWt u 0)] cycWord Q Λ u)
    (π : cycWord Q Λ u →ₗ[CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^
      Λ (Fin.last ℓ) j) (wordWt u 0)] Y₀)
    (hπι : π.comp ι = LinearMap.id) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor (A := ℤ) ℤ n).obj
      ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q Λ ν)
        ((reflectOne Q Λ hQ hρ).obj (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀))).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (TensorProductAlgebra k Q Λ ν)).obj
          (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀))))) :=
  isZero_derivedTensorHomology_reflectOne_tensorStd_of_ne_zero Q Λ hQ hρ hR
    (rouquierStandardCovers hR hQ Λ ν) u h₀ t ht Y₀ ι π hπι n hn

variable [HasExt.{v} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν))]

include hρ in
/-- **`Tor₀` on the diagonal over `ℤ`** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22, the diagonal `E²` term): under the hypotheses of the second clause of
Proposition 7.8 (`exists_stdResolution_last`) for Rouquier `Q`, the degree-zero homology of
`M^r ⊗ᴸ_T M` computed over `ℤ`, `M = S(T^{λ'} e(t) ⊠ Y₀)` the last term, is additively
isomorphic to `k`. The `k`-dimension count is `finrank_tensorProductOver_reflectOne_last`;
the degree-zero comparison is `ambientDerivedTensorH0Equiv` over `ℤ`. -/
theorem nonempty_addEquiv_derivedTensorHomology_int_reflectOne_last
    {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
    (X : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)) [FiniteDimensional k X]
    (hX : ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s), ¬HasLastRed s →
      ∀ x : X, loadingIdem Q Λ s hs • x = 0)
    (u : List I) (h₀ : 0 + wordWt u 0 = ν) (t : Seq (stendhalWeight ℓ 0)) (ht : IsRedOrdered t)
    (het : TensorProductAlgebra.mk Q (Λ ∘ Fin.castSucc) 0 (StendhalAlgebra.e t ht) = 1)
    (Y₀ : ModuleCat.{0} (CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^
      Λ (Fin.last ℓ) j) (wordWt u 0)))
    (hss : ∀ (M : Type) [AddCommGroup M] [Module (CycKLR k Q (fun j =>
      (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j) (wordWt u 0)) M]
      [Module.Finite (CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^
        Λ (Fin.last ℓ) j) (wordWt u 0)) M],
      ∃ n : ℕ, Nonempty (M ≃ₗ[CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^
        Λ (Fin.last ℓ) j) (wordWt u 0)] (Fin n → Y₀)))
    {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (ι : J → (Y₀ →ₗ[CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^
      Λ (Fin.last ℓ) j) (wordWt u 0)] cycWord Q Λ u))
    (π : J → (cycWord Q Λ u →ₗ[CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^
      Λ (Fin.last ℓ) j) (wordWt u 0)] Y₀))
    (hιπ : ∀ i j, (π j).comp (ι i) = if i = j then LinearMap.id else 0)
    (htot : ∑ j, (ι j).comp (π j) = LinearMap.id)
    (htop : Module.finrank k (Ext.{v} (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀) X
      (Multiset.card ν)) = 1) :
    Nonempty ((homologyFunctor (A := ℤ) ℤ 0).obj
      ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q Λ ν)
        ((reflectOne Q Λ hQ hρ).obj (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀))).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (TensorProductAlgebra k Q Λ ν)).obj
          (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀)))) ≃+ k) := by
  have h1 := finrank_tensorProductOver_reflectOne_last Q Λ hQ hρ hR X hX u h₀ t ht het Y₀ hss
    ι π hιπ htot htop
  have := Module.finite_of_finrank_eq_succ h1
  let e₀ := ambientDerivedTensorH0Equiv (k := ℤ) (A := TensorProductAlgebra k Q Λ ν)
    (N := (reflectOne Q Λ hQ hρ).obj (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀))
    (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀)
  let e₁ := LinearEquiv.ofFinrankEq (TensorProductOver (TensorProductAlgebra k Q Λ ν)
    ((reflectOne Q Λ hQ hρ).obj (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀))
    (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀)) k (by rw [h1, Module.finrank_self])
  exact ⟨e₀.toAddEquiv.trans e₁.toAddEquiv⟩

include hρ in
/-- **The diagonal term is concentrated in degree zero, over `ℤ`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, the diagonal `E²` term): under the
hypotheses of the second clause of Proposition 7.8 (`exists_stdResolution_last`) for Rouquier
`Q`, `Tor_n^ℤ(M^r, M) = 0` for `n ≠ 0` and `Tor_0^ℤ(M^r, M) ≃+ k`, for the last term
`M = S(T^{λ'} e(t) ⊠ Y₀)`. Both are computed with the coefficient ring `ℤ` of the off-diagonal
Tor lemmas. -/
theorem torConcentrated_reflectOne_last
    [HasDerivedCategory.{w, 0}
      (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) (List.map (1 : Perm (Fin (ℓ + 1)))
        (List.finRange (ℓ + 1))))]
    {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
    (X : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)) [FiniteDimensional k X]
    (hX : ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s), ¬HasLastRed s →
      ∀ x : X, loadingIdem Q Λ s hs • x = 0)
    (u : List I) (h₀ : 0 + wordWt u 0 = ν) (t : Seq (stendhalWeight ℓ 0)) (ht : IsRedOrdered t)
    (het : TensorProductAlgebra.mk Q (Λ ∘ Fin.castSucc) 0 (StendhalAlgebra.e t ht) = 1)
    (Y₀ : ModuleCat.{0} (CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^
      Λ (Fin.last ℓ) j) (wordWt u 0)))
    (hss : ∀ (M : Type) [AddCommGroup M] [Module (CycKLR k Q (fun j =>
      (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j) (wordWt u 0)) M]
      [Module.Finite (CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^
        Λ (Fin.last ℓ) j) (wordWt u 0)) M],
      ∃ n : ℕ, Nonempty (M ≃ₗ[CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^
        Λ (Fin.last ℓ) j) (wordWt u 0)] (Fin n → Y₀)))
    {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (ι : J → (Y₀ →ₗ[CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^
      Λ (Fin.last ℓ) j) (wordWt u 0)] cycWord Q Λ u))
    (π : J → (cycWord Q Λ u →ₗ[CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^
      Λ (Fin.last ℓ) j) (wordWt u 0)] Y₀))
    (hιπ : ∀ i j, (π j).comp (ι i) = if i = j then LinearMap.id else 0)
    (htot : ∑ j, (ι j).comp (π j) = LinearMap.id)
    (htop : Module.finrank k (Ext.{v} (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀) X
      (Multiset.card ν)) = 1) :
    (∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor (A := ℤ) ℤ n).obj
      ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q Λ ν)
        ((reflectOne Q Λ hQ hρ).obj (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀))).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (TensorProductAlgebra k Q Λ ν)).obj
          (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀)))))) ∧
    Nonempty ((homologyFunctor (A := ℤ) ℤ 0).obj
      ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q Λ ν)
        ((reflectOne Q Λ hQ hρ).obj (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀))).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (TensorProductAlgebra k Q Λ ν)).obj
          (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀)))) ≃+ k) := by
  obtain ⟨j₀⟩ := (inferInstance : Nonempty J)
  refine ⟨fun n hn => isZero_derivedTensorHomology_reflectOne_last_of_ne_zero Q Λ hQ hρ hR u h₀
    t ht Y₀ (ι j₀) (π j₀) (by simpa using hιπ j₀ j₀) n hn, ?_⟩
  exact nonempty_addEquiv_derivedTensorHomology_int_reflectOne_last Q Λ hQ hρ hR X hX u h₀ t ht
    het Y₀ hss ι π hιπ htot htop

end Diagonal

end Categorification.Stendhal
