/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveTorDevissage
import Categorification.WeightedKLR.Rigidity.RigidityExtLastTerm

/-!
# Proposition 7.22 (c): the S-move Tor reduced to the diagonal pair

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c). This file plugs the resolutions of Proposition 7.8
(`exists_stdResolution` for the left module `L` over `T^{λ_2, λ_3}(ν)`, and its second clause
`exists_stdResolution_last` for the right module `L'` over `T^{λ_1, λ_2}(ν)`, whose last term is
`S(T^{λ_1} e(t) ⊠ Y₀)`) into the dévissage of `SMoveTorDevissage`. For a Rouquier choice of
`Q` every route hypothesis of the Tor lemmas and of Proposition 7.6 is discharged, and the
S-move Tor `H^n((SMove.leftStd L)^r ⊗ᴸ SMove.rightStd L')` is the Tor of the diagonal pair
`((SMove.leftStd M_0)^r, SMove.rightStd S(T^{λ_1} e(t) ⊠ Y₀))`, shifted by `|ν|`.

Comparison with Webster v3, Proposition 7.22 (the step at `λ₁ = λ₂ = ∅`): the statement there
is an isomorphism of graded modules `X ⊗ᴸ Y ≅ (corner)[−2ρ^∨](2⟨λ, ρ⟩)`, for `g` of finite type
and any `Q`. Here: (1) ungraded (no internal shift); (2) the homological shift `|ν| = 2ρ^∨(λ)`
is kept; (3) Tor over `ℤ`, so the identifications are of `ℤ`-modules; (4) Rouquier `Q`; (5) the
diagonal pair (step R5: no higher Tor, `Tor₀` one-dimensional) is not computed here. The labels:
`coevaluationLabels ν = ![λ, λ*]` (`RigidityExtHead`), the order `(λ, λ*)` of the right module
`L'` over `T^{λ_1, λ_2}`; the left module `L` must live over `(λ*, λ)`.

## Main results

* `SMove.exists_stdSum_linearEquiv_derivedTensorHomology_reflect_leftStd_rightStd`.
* `SMove.exists_stdSum_isZero_derivedTensorHomology_reflect_leftStd_rightStd`: concentration in
  degree `-|ν|`, given the vanishing of the higher Tor of the diagonal pair.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.SMove

open CategoryTheory CategoryTheory.Limits Abelian KLR ModuleFiltration Equiv
  BraidedStendhalAlgebra
open DG DG.DerivedCategory
open scoped TensorProduct DG.DegreeZero

universe w v

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) (Λ : Fin (1 + (1 + 1)) → I →₀ ℕ) {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight (1 + 1 + 1) ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ)
  [HasDerivedCategory.{w, 0}
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (ν := ν)
      (List.map (1 : Perm (Fin (1 + 1 + 1))) (List.finRange (1 + 1 + 1))))]
  [HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν)]
  [HasDerivedCategory.{w, 0} ℤ]
  [HasExt.{v} (ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) ν))]
  [HasExt.{v} (ModuleCat.{0} (TensorProductAlgebra k Q
    ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc) ν))]

omit [DecidableEq I] in
/-- The labels `(λ_1, λ_2)` of the right module of the S-move. -/
abbrev rightLabels : Fin (1 + 1) → I →₀ ℕ := (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc

/-- The cyclotomic KLR algebra `R^{λ_2}(β)` of the last red strand of the right module. -/
abbrev rightCyc (β : Multiset I) : Type :=
  CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^ rightLabels Λ (Fin.last 1) j) β

include hρ in
/-- **Proposition 7.22 (c), reduction to the diagonal pair** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.22, gap (c), dévissage in place of the spectral sequence). Let `L` over
`T^{λ_2, λ_3}(ν)` and `L'` over `T^{λ_1, λ_2}(ν)` be finite-dimensional and killed by every
loading idempotent with a black strand right of the last red strand, and let `L'` satisfy the
hypotheses of the second clause of Proposition 7.8 (`exists_stdResolution_last`), with last
term `M'_{|ν|} = S(T^{λ_1} e(t) ⊠ Y₀)`. For Rouquier `Q` there is a first term `M_0` of a
resolution of `L` as in Proposition 7.8 (a `StdSum` at position `|ν| + 1`) with
`H^n((SMove.leftStd L)^r ⊗ᴸ SMove.rightStd L') ≅
  H^{n + |ν|}((SMove.leftStd M_0)^r ⊗ᴸ SMove.rightStd M'_{|ν|})` over `ℤ` for every `n`.

Route hypotheses: a Rouquier choice of `Q` (it discharges the route hypothesis
`AllFiniteDeltaInjective` of Proposition 7.6 and the hypotheses `DC`, `hold` of the Tor
lemmas). The diagonal pair is not computed here (step R5). -/
theorem exists_stdSum_linearEquiv_derivedTensorHomology_reflect_leftStd_rightStd
    {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
    (L : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) ν)) [FiniteDimensional k L]
    (hL : ∀ (s : Seq (stendhalWeight (1 + 1) ν)) (hs : IsRedOrdered s), ¬HasLastRed s →
      ∀ x : L, loadingIdem Q (Λ ∘ Fin.natAdd 1) s hs • x = 0)
    (L' : ModuleCat.{0} (TensorProductAlgebra k Q (rightLabels Λ) ν))
    [FiniteDimensional k L']
    (hL' : ∀ (s : Seq (stendhalWeight (1 + 1) ν)) (hs : IsRedOrdered s), ¬HasLastRed s →
      ∀ x : L', loadingIdem Q (rightLabels Λ) s hs • x = 0)
    (u : List I) (h₀ : 0 + wordWt u 0 = ν) (t : Seq (stendhalWeight 1 0)) (ht : IsRedOrdered t)
    (het : TensorProductAlgebra.mk Q ((rightLabels Λ) ∘ Fin.castSucc) 0
      (StendhalAlgebra.e t ht) = 1)
    (Y₀ : ModuleCat.{0} (rightCyc Q Λ (wordWt u 0)))
    (hss : ∀ (M : Type) [AddCommGroup M] [Module (rightCyc Q Λ (wordWt u 0)) M]
      [Module.Finite (rightCyc Q Λ (wordWt u 0)) M],
      ∃ n : ℕ, Nonempty (M ≃ₗ[rightCyc Q Λ (wordWt u 0)] (Fin n → Y₀)))
    {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (ι : J → (Y₀ →ₗ[rightCyc Q Λ (wordWt u 0)] cycWord Q (rightLabels Λ) u))
    (π : J → (cycWord Q (rightLabels Λ) u →ₗ[rightCyc Q Λ (wordWt u 0)] Y₀))
    (hιπ : ∀ i j, (π j).comp (ι i) = if i = j then LinearMap.id else 0)
    (htot : ∑ j, (ι j).comp (π j) = LinearMap.id)
    (htop : Module.finrank k (Ext.{v}
      (tensorStd Q (rightLabels Λ) hQ h₀ (oldProj Q (rightLabels Λ) 0 t ht) Y₀) L'
      (Multiset.card ν)) = 1) :
    ∃ M₀ : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) ν),
      StdSum Q (Λ ∘ Fin.natAdd 1) hQ (Multiset.card ν + 1) M₀ ∧ ∀ n : ℤ,
      Nonempty ((homologyFunctor (A := ℤ) ℤ (n)).obj
        ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν)
          ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ).obj
            ((leftStd Q hQ Λ ν).obj L))).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
            ((rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν).obj
              L')))) ≃ₗ[ℤ]
        (homologyFunctor (A := ℤ) ℤ (n + Multiset.card ν)).obj
        ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν)
          ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ).obj
            ((leftStd Q hQ Λ ν).obj M₀))).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
            ((rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν).obj
              (tensorStd Q (rightLabels Λ) hQ h₀ (oldProj Q (rightLabels Λ) 0 t ht) Y₀)))))) := by
  have hall : AllFiniteDeltaInjective Q (Λ ∘ Fin.natAdd 1) hQ := by
    convert allFiniteDeltaInjective_of_rouquier hR hQ
  have hall' : AllFiniteDeltaInjective Q (rightLabels Λ) hQ := by
    convert allFiniteDeltaInjective_of_rouquier hR hQ
  obtain ⟨S, h0, hs, hS, hstd, hz⟩ :=
    exists_stdResolution.{v} Q (Λ ∘ Fin.natAdd 1) hQ hR hall L hL
  obtain ⟨S', h0', hs', hS', hstd', hz', ⟨eN⟩, -⟩ :=
    exists_stdResolution_last.{v} Q (rightLabels Λ) hQ hR hall' L' hL'
      u h₀ t ht het Y₀ hss ι π hιπ htot htop
  refine ⟨(S 0).X₂, by simpa using hstd 0 (Nat.zero_le _), fun n => ?_⟩
  obtain ⟨e⟩ := nonempty_linearEquiv_derivedTensorHomology_reflect_leftStd_rightStd.{w} Q hQ Λ
    hρ S h0 hs hS hstd hz S' h0' hs' hS' hstd' hz' hR n
  exact ⟨e.trans ((homologyFunctor (A := ℤ) ℤ _).mapIso ((derivedTensor.{w} ℤ _ _).mapIso
    (DG.DerivedCategory.Q.mapIso ((degreeZeroModuleFunctor _).mapIso
      ((rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν).mapIso eN))))).toLinearEquiv⟩

include hρ in
/-- **Proposition 7.22 (c), concentration modulo the diagonal pair** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, gap (c)): under the hypotheses of
`exists_stdSum_linearEquiv_derivedTensorHomology_reflect_leftStd_rightStd`, there is a first
term `M_0` of a resolution of `L` as in Proposition 7.8 such that
`H^{-|ν|}((SMove.leftStd L)^r ⊗ᴸ SMove.rightStd L') ≅ Tor₀` of the diagonal pair, and, if the
diagonal pair has no higher Tor (route hypothesis, step R5), `(SMove.leftStd L)^r ⊗ᴸ
SMove.rightStd L'` has no cohomology outside degree `-|ν|`. -/
theorem exists_stdSum_isZero_derivedTensorHomology_reflect_leftStd_rightStd
    {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
    (L : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) ν)) [FiniteDimensional k L]
    (hL : ∀ (s : Seq (stendhalWeight (1 + 1) ν)) (hs : IsRedOrdered s), ¬HasLastRed s →
      ∀ x : L, loadingIdem Q (Λ ∘ Fin.natAdd 1) s hs • x = 0)
    (L' : ModuleCat.{0} (TensorProductAlgebra k Q (rightLabels Λ) ν))
    [FiniteDimensional k L']
    (hL' : ∀ (s : Seq (stendhalWeight (1 + 1) ν)) (hs : IsRedOrdered s), ¬HasLastRed s →
      ∀ x : L', loadingIdem Q (rightLabels Λ) s hs • x = 0)
    (u : List I) (h₀ : 0 + wordWt u 0 = ν) (t : Seq (stendhalWeight 1 0)) (ht : IsRedOrdered t)
    (het : TensorProductAlgebra.mk Q ((rightLabels Λ) ∘ Fin.castSucc) 0
      (StendhalAlgebra.e t ht) = 1)
    (Y₀ : ModuleCat.{0} (rightCyc Q Λ (wordWt u 0)))
    (hss : ∀ (M : Type) [AddCommGroup M] [Module (rightCyc Q Λ (wordWt u 0)) M]
      [Module.Finite (rightCyc Q Λ (wordWt u 0)) M],
      ∃ n : ℕ, Nonempty (M ≃ₗ[rightCyc Q Λ (wordWt u 0)] (Fin n → Y₀)))
    {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (ι : J → (Y₀ →ₗ[rightCyc Q Λ (wordWt u 0)] cycWord Q (rightLabels Λ) u))
    (π : J → (cycWord Q (rightLabels Λ) u →ₗ[rightCyc Q Λ (wordWt u 0)] Y₀))
    (hιπ : ∀ i j, (π j).comp (ι i) = if i = j then LinearMap.id else 0)
    (htot : ∑ j, (ι j).comp (π j) = LinearMap.id)
    (htop : Module.finrank k (Ext.{v}
      (tensorStd Q (rightLabels Λ) hQ h₀ (oldProj Q (rightLabels Λ) 0 t ht) Y₀) L'
      (Multiset.card ν)) = 1) :
    ∃ M₀ : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) ν),
      StdSum Q (Λ ∘ Fin.natAdd 1) hQ (Multiset.card ν + 1) M₀ ∧
      Nonempty ((homologyFunctor (A := ℤ) ℤ (-(Multiset.card ν : ℤ))).obj
        ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν)
          ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ).obj
            ((leftStd Q hQ Λ ν).obj L))).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
            ((rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν).obj
              L')))) ≃ₗ[ℤ]
        (homologyFunctor (A := ℤ) ℤ (0)).obj
        ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν)
          ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ).obj
            ((leftStd Q hQ Λ ν).obj M₀))).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
            ((rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν).obj
              (tensorStd Q (rightLabels Λ) hQ h₀ (oldProj Q (rightLabels Λ) 0 t ht) Y₀)))))) ∧
      ((∀ m : ℤ, m ≠ 0 → IsZero ((homologyFunctor (A := ℤ) ℤ (m)).obj
        ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν)
          ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ).obj
            ((leftStd Q hQ Λ ν).obj M₀))).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
            ((rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν).obj
              (tensorStd Q (rightLabels Λ) hQ h₀ (oldProj Q (rightLabels Λ) 0 t ht) Y₀))))))) →
        ∀ n : ℤ, n ≠ -(Multiset.card ν : ℤ) → IsZero ((homologyFunctor (A := ℤ) ℤ (n)).obj
        ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν)
          ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ).obj
            ((leftStd Q hQ Λ ν).obj L))).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
            ((rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν).obj
              L')))))) := by
  obtain ⟨M₀, hM₀, he⟩ :=
    exists_stdSum_linearEquiv_derivedTensorHomology_reflect_leftStd_rightStd.{w, v} Q hQ Λ hρ
      hR L hL L' hL' u h₀ t ht het Y₀ hss ι π hιπ htot htop
  refine ⟨M₀, hM₀, ?_, fun hdiag n hn => ?_⟩
  · obtain ⟨e⟩ := he (-(Multiset.card ν : ℤ))
    exact ⟨e.trans (eqToIso (congrArg (fun d : ℤ => (homologyFunctor (A := ℤ) ℤ d).obj _)
      (neg_add_cancel (Multiset.card ν : ℤ)))).toLinearEquiv⟩
  · obtain ⟨e⟩ := he n
    exact (hdiag _ (by omega)).of_iso e.toModuleIso

end Categorification.Stendhal.SMove
