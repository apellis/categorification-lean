/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveLeftStdStandardTor
import Categorification.WeightedKLR.Rigidity.SMoveTorAssembly
import Categorification.WeightedKLR.Rigidity.SMoveDiagonalStandard

/-!
# The diagonal pair of the S-move has no higher Tor

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c), step R5. The diagonal pair of the dévissage
(`SMove.exists_stdSum_isZero_derivedTensorHomology_reflect_leftStd_rightStd`) is the coefficient
`(SMove.leftStd M_0)^r` against the module `SMove.rightStd S(T^{λ_1} e(t) ⊠ Y₀)`, with `Y₀` a
summand of the cyclotomic projective `R^{λ_2} e(𝐮)` (`cycWord`).

* `SMove.rightStd S(T^{λ_1} e(t) ⊠ R^{λ_2} e(𝐮))` is the standard module `S_s` of a loading
  `s = (red₁ red₂ 𝐮' red₃)` (`SMove.exists_rightStd_tensorStd_cycWord_equiv`): with no black
  strand, `T^{λ_1}(0) e(t)` is the standard of its loading, then
  `nonempty_stdLayerModule_twoPiece_equiv` and `SMove.nonempty_rightStd_equiv_of_equiv`.
* Every black strand of `s` is left of the last red strand, so the coefficient
  `(SMove.leftStd N)^r` has no higher Tor against `S_s`, for every `N`
  (`SMove.isZero_derivedTensorHomology_reflectOne_leftStd_leftStandard`).
* Higher Tor vanishing passes to retracts of the module
  (`isZero_derivedTensorHomology_of_module_retract`), and `S(T^{λ_1} e(t) ⊠ Y₀)` is a retract
  of `S(T^{λ_1} e(t) ⊠ R^{λ_2} e(𝐮))` through `π ∘ ι = id`.

This discharges the route hypothesis `hdiag` of
`SMove.exists_stdSum_isZero_derivedTensorHomology_reflect_leftStd_rightStd`: for Rouquier `Q`
the S-move Tor `(SMove.leftStd L)^r ⊗ᴸ SMove.rightStd L'` is concentrated in degree `-|ν|`
(`SMove.exists_stdSum_derivedTensorHomology_concentrated`), and its cohomology there is the
`Tor₀` of the diagonal pair. The `Tor₀` count (Webster's one-dimensionality) is not computed
here.

Route hypothesis: a Rouquier choice of `Q`. Tor is over `ℤ`, as in the other Tor lemmas of the
S-move; the statement is ungraded.

## Main results

* `isZero_derivedTensorHomology_of_module_retract`.
* `SMove.exists_rightStd_tensorStd_cycWord_equiv`.
* `SMove.isZero_derivedTensorHomology_reflect_leftStd_rightStd_tensorStd`.
* `SMove.exists_stdSum_derivedTensorHomology_concentrated`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits KLR Equiv MulOpposite BraidedStendhalAlgebra
open DG DG.DerivedCategory
open scoped DG.DegreeZero

universe w v

section Retract

variable {B : Type} [Ring B] [HasDerivedCategory.{w, 0} B] [HasDerivedCategory.{w, 0} ℤ]

/-- **Vanishing of derived tensor cohomology passes to retracts of the module**: if
`a ≫ b = 𝟙 Y` for `a : Y ⟶ Y'`, `b : Y' ⟶ Y`, and `H^n(N ⊗ᴸ Y') = 0`, then
`H^n(N ⊗ᴸ Y) = 0`. -/
theorem isZero_derivedTensorHomology_of_module_retract (N : ModuleCat.{0} Bᵐᵒᵖ)
    {Y Y' : ModuleCat.{0} B} (a : Y ⟶ Y') (b : Y' ⟶ Y) (hab : a ≫ b = 𝟙 Y) (n : ℤ)
    (hY' : IsZero ((homologyFunctor (A := ℤ) ℤ n).obj ((derivedTensor.{w} ℤ B N).obj
      (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor B).obj Y'))))) :
    IsZero ((homologyFunctor (A := ℤ) ℤ n).obj ((derivedTensor.{w} ℤ B N).obj
      (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor B).obj Y)))) := by
  let F := degreeZeroModuleFunctor B ⋙ DG.DerivedCategory.Q ⋙
    derivedTensor.{w} ℤ B N ⋙ homologyFunctor (A := ℤ) ℤ n
  have hF : F.map a ≫ F.map b = 𝟙 _ := by rw [← F.map_comp, hab, F.map_id]
  have : Mono (F.map a) := mono_of_mono_fac hF
  exact IsZero.of_mono (F.map a) hY'

end Retract

namespace SMove

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) (Λ : Fin (1 + (1 + 1)) → I →₀ ℕ) {ν : Multiset I}

local notation "Λ₃" => (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1) : Fin (1 + 1 + 1) → I →₀ ℕ)

/-- With no black strand, `T^{λ_1}(0) e(t)` is the standard module of its loading. -/
def oldProjZeroStandardEquiv (Λ' : Fin (1 + 1) → I →₀ ℕ)
    (t : Seq (stendhalWeight 1 (0 : Multiset I))) (ht : IsRedOrdered t) :
    oldProj Q Λ' 0 t ht ≃ₗ[TensorProductAlgebra k Q (Λ' ∘ Fin.castSucc) 0]
      ModuleCat.of (TensorProductAlgebra k Q (Λ' ∘ Fin.castSucc) 0)
        (leftStandard Q (Λ' ∘ Fin.castSucc) t ht) := by
  exact (Submodule.quotEquivOfEqBot _ (by
    rw [leftUpper_eq_bot_of_one_zero Q (Λ' ∘ Fin.castSucc) t ht, Submodule.comap_bot,
      Submodule.ker_subtype])).symm

/-- **`SMove.rightStd S(T^{λ_1} e(t) ⊠ R^{λ_2} e(𝐮))` is a standard module** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, the diagonal `E²` term): it is `S_s` for a
loading `s` of the three red strands with every black strand left of the last red strand. -/
theorem exists_rightStd_tensorStd_cycWord_equiv (u : List I) (h₀ : 0 + wordWt u 0 = ν)
    (t : Seq (stendhalWeight 1 0)) (ht : IsRedOrdered t) :
    ∃ (s : Seq (stendhalWeight (1 + 1 + 1) ν)) (hs : IsRedOrdered s),
      (∀ i, blackCount s (Fin.last 2) i = ν.count i) ∧
      Nonempty ((rightStd Q hQ Λ₃ ν).obj
          (tensorStd Q (rightLabels Λ) hQ h₀ (oldProj Q (rightLabels Λ) 0 t ht)
            (cycWord Q (rightLabels Λ) u)) ≃ₗ[TensorProductAlgebra k Q Λ₃ ν]
        ModuleCat.of (TensorProductAlgebra k Q Λ₃ ν) (leftStandard Q Λ₃ s hs)) := by
  obtain ⟨g⟩ := nonempty_cycWord_equiv_cycProj Q (rightLabels Λ) u
  let u' := KLRAlgebra.Seq.ofList u.reverse (coe_reverse_eq_wordWt u)
  obtain ⟨g₂⟩ := nonempty_stdLayerModule_twoPiece_equiv Q (rightLabels Λ) hQ h₀ ht u'
  let f := (stdLayerEquiv Q (rightLabels Λ) hQ h₀
    (tensorFactorCongr Q (rightLabels Λ)
      (oldProjZeroStandardEquiv Q (rightLabels Λ) t ht) g)).trans g₂
  obtain ⟨g₃⟩ := nonempty_rightStd_equiv_of_equiv Q hQ Λ₃ ν _ _ default f
  exact ⟨_, _, fun i => blackCount_twoPieceLabel_last (add_zero ν) default _ i, ⟨g₃⟩⟩

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight (1 + 1 + 1) ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ)
  [HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν)]
  [HasDerivedCategory.{w, 0} ℤ]

include hρ in
/-- **The diagonal pair has no higher Tor** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22, gap (c), step R5): for Rouquier `Q`, every module `N` over `T^{λ_2, λ_3}(ν)`
and a summand `Y₀` of `R^{λ_2} e(𝐮)` (`π ∘ ι = id`),
`Tor_n^ℤ((SMove.leftStd N)^r, SMove.rightStd S(T^{λ_1} e(t) ⊠ Y₀)) = 0` for `n ≠ 0`.

Route hypothesis: a Rouquier choice of `Q`. -/
theorem isZero_derivedTensorHomology_reflect_leftStd_rightStd_tensorStd
    {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
    (N : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) ν))
    (u : List I) (h₀ : 0 + wordWt u 0 = ν) (t : Seq (stendhalWeight 1 0)) (ht : IsRedOrdered t)
    (Y₀ : ModuleCat.{0} (rightCyc Q Λ (wordWt u 0)))
    (ι : Y₀ →ₗ[rightCyc Q Λ (wordWt u 0)] cycWord Q (rightLabels Λ) u)
    (π : cycWord Q (rightLabels Λ) u →ₗ[rightCyc Q Λ (wordWt u 0)] Y₀)
    (hπι : π.comp ι = LinearMap.id) (m : ℤ) (hm : m ≠ 0) :
    IsZero ((homologyFunctor (A := ℤ) ℤ m).obj
      ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q Λ₃ ν)
        ((reflectOne Q Λ₃ hQ hρ).obj ((leftStd Q hQ Λ ν).obj N))).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
          ((rightStd Q hQ Λ₃ ν).obj
            (tensorStd Q (rightLabels Λ) hQ h₀ (oldProj Q (rightLabels Λ) 0 t ht) Y₀)))))) := by
  obtain ⟨s, hs, hlast, ⟨e⟩⟩ := exists_rightStd_tensorStd_cycWord_equiv Q hQ Λ u h₀ t ht
  let X := oldProj Q (rightLabels Λ) 0 t ht
  let R := rightStd Q hQ Λ₃ ν
  let a := R.map (ModuleCat.ofHom (tensorStdMapRight Q (rightLabels Λ) hQ h₀ X ι))
  let b := R.map (ModuleCat.ofHom (tensorStdMapRight Q (rightLabels Λ) hQ h₀ X π))
  have hab : a ≫ b = 𝟙 _ := by
    rw [← R.map_comp, ← R.map_id]
    congr 1
    refine ModuleCat.hom_ext ?_
    change (tensorStdMapRight Q (rightLabels Λ) hQ h₀ X π).comp
      (tensorStdMapRight Q (rightLabels Λ) hQ h₀ X ι) = LinearMap.id
    rw [← tensorStdMapRight_comp, hπι, tensorStdMapRight_id]
  have h₁ := isZero_derivedTensorHomology_reflectOne_leftStd_leftStandard.{w} Q hQ Λ hρ hR N s hs
    hlast m hm
  have h₂ : IsZero ((homologyFunctor (A := ℤ) ℤ m).obj
      ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q Λ₃ ν)
        ((reflectOne Q Λ₃ hQ hρ).obj ((leftStd Q hQ Λ ν).obj N))).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
          ((rightStd Q hQ Λ₃ ν).obj (tensorStd Q (rightLabels Λ) hQ h₀ X
            (cycWord Q (rightLabels Λ) u))))))) :=
    h₁.of_iso ((homologyFunctor (A := ℤ) ℤ m).mapIso ((derivedTensor.{w} ℤ _ _).mapIso
      (DG.DerivedCategory.Q.mapIso ((degreeZeroModuleFunctor _).mapIso e.toModuleIso))))
  exact isZero_derivedTensorHomology_of_module_retract (B := TensorProductAlgebra k Q Λ₃ ν)
    ((reflectOne Q Λ₃ hQ hρ).obj ((leftStd Q hQ Λ ν).obj N)) a b hab m h₂


section Assembly

open Abelian

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable [HasDerivedCategory.{w, 0}
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (ν := ν)
      (List.map (1 : Perm (Fin (1 + 1 + 1))) (List.finRange (1 + 1 + 1))))]
  [HasExt.{v} (ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) ν))]
  [HasExt.{v} (ModuleCat.{0} (TensorProductAlgebra k Q
    ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc) ν))]

include hρ in
/-- **Proposition 7.22 (c): the S-move Tor is concentrated in one degree** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, gap (c)). Under the hypotheses of
`exists_stdSum_isZero_derivedTensorHomology_reflect_leftStd_rightStd` (`L` over
`T^{λ_2, λ_3}(ν)`, `L'` over `T^{λ_1, λ_2}(ν)` as in the second clause of Proposition 7.8),
for Rouquier `Q` there is a first term `M_0` of a resolution of `L` as in Proposition 7.8 such
that `H^{-|ν|}((SMove.leftStd L)^r ⊗ᴸ SMove.rightStd L')` is the `Tor₀` of the diagonal pair
`((SMove.leftStd M_0)^r, SMove.rightStd S(T^{λ_1} e(t) ⊠ Y₀))`, and
`(SMove.leftStd L)^r ⊗ᴸ SMove.rightStd L'` has no cohomology outside degree `-|ν|`. The
diagonal hypothesis `hdiag` of the source lemma is discharged by
`isZero_derivedTensorHomology_reflect_leftStd_rightStd_tensorStd`.

Comparison with Webster v3, Proposition 7.22 (as in `SMoveTorAssembly`): ungraded, Tor over
`ℤ`, Rouquier `Q`; the dimension of the `Tor₀` (one) is not computed here.
Route hypothesis: a Rouquier choice of `Q`. -/
theorem exists_stdSum_derivedTensorHomology_concentrated
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
      ∀ n : ℤ, n ≠ -(Multiset.card ν : ℤ) → IsZero ((homologyFunctor (A := ℤ) ℤ (n)).obj
        ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν)
          ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ).obj
            ((leftStd Q hQ Λ ν).obj L))).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
            ((rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν).obj
              L'))))) := by
  obtain ⟨M₀, hM₀, he, hconc⟩ :=
    exists_stdSum_isZero_derivedTensorHomology_reflect_leftStd_rightStd.{w, v} Q hQ Λ hρ
      hR L hL L' hL' u h₀ t ht het Y₀ hss ι π hιπ htot htop
  obtain ⟨j⟩ := ‹Nonempty J›
  have hπι : (π j).comp (ι j) = LinearMap.id := by simpa using hιπ j j
  exact ⟨M₀, hM₀, he, hconc fun m hm =>
    isZero_derivedTensorHomology_reflect_leftStd_rightStd_tensorStd.{w} Q hQ Λ hρ hR M₀ u h₀
      t ht Y₀ (ι j) (π j) hπι m hm⟩

end Assembly

end SMove

end Categorification.Stendhal
