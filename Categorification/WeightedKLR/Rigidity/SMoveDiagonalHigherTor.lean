/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorCoefficientRetract
import Categorification.WeightedKLR.Rigidity.SMoveStandardizationProjTor
import Categorification.WeightedKLR.Rigidity.SMoveStdLayerSeparation
import Categorification.WeightedKLR.Rigidity.RigidityExtStandardSum
import Categorification.WeightedKLR.RedStrands.StandardStratificationStd

/-!
# No higher Tor on the diagonal of the S-move

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c), step R5, the diagonal `E²` term. Let `M = S(T^{λ'} e(t) ⊠ Y₀)`,
`Y₀` a summand of `R^{λ_ℓ} e(u)`; this is the last term of the resolution of Proposition 7.8.
Then `Tor_n(M^r, M) = 0` for `n ≠ 0`, `M^r` the reflection of `M`
(`isZero_derivedTensorHomology_reflectOne_tensorStd_of_ne_zero`).

`M` is a retract of `N = S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u))`, so `M^r` is a retract of `N^r`. The
standard filtration of `N` (Proposition 5.20) and its reflection give `Tor_n(N^r, N) = 0` for
`n ≠ 0` (`isZero_derivedTensorHomology_stdLayer_tensorProj_of_ne_zero`), and vanishing passes to
retracts in each argument (`isZero_derivedTensorHomology_coefficient_retract` for the first).
The ordered standard covers `D` of the left standards are a hypothesis, as in the other Tor
lemmas of this step.
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits KLR ModuleFiltration Equiv BraidedStendhalAlgebra
open DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

universe w

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q) {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ)
  [HasDerivedCategory.{w, 0}
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) (List.map (1 : Perm (Fin (ℓ + 1)))
      (List.finRange (ℓ + 1))))]
  [HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q Λ ν)] [HasDerivedCategory.{w, 0} ℤ]

omit [HasDerivedCategory.{w, 0}
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) (List.map (1 : Perm (Fin (ℓ + 1)))
      (List.finRange (ℓ + 1))))] in
/-- **Vanishing passes to retracts in both arguments** of `Tor` against reflections: if
`b ∘ a = id` for `a : M → N`, `b : N → M`, and `Tor_n(N^r, N) = 0`, then `Tor_n(M^r, M) = 0`. -/
theorem isZero_derivedTensorHomology_reflectOne_retract
    {M N : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)} (a : M ⟶ N) (b : N ⟶ M)
    (hab : a ≫ b = 𝟙 M) (n : ℤ) (hN : IsZero ((homologyFunctor (A := ℤ) ℤ n).obj
        ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q Λ ν) ((reflectOne Q Λ hQ hρ).obj N)).obj
          (DG.DerivedCategory.Q.obj
            ((degreeZeroModuleFunctor (TensorProductAlgebra k Q Λ ν)).obj N))))) :
    IsZero ((homologyFunctor (A := ℤ) ℤ n).obj
        ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q Λ ν) ((reflectOne Q Λ hQ hρ).obj M)).obj
          (DG.DerivedCategory.Q.obj
            ((degreeZeroModuleFunctor (TensorProductAlgebra k Q Λ ν)).obj M)))) := by
  -- The second argument: `Tor_n(N^r, M)` is a retract of `Tor_n(N^r, N)`.
  let F := degreeZeroModuleFunctor (TensorProductAlgebra k Q Λ ν) ⋙ DG.DerivedCategory.Q ⋙
    derivedTensor.{w} ℤ (TensorProductAlgebra k Q Λ ν) ((reflectOne Q Λ hQ hρ).obj N) ⋙
    homologyFunctor (A := ℤ) ℤ n
  have hF : F.map a ≫ F.map b = 𝟙 _ := by rw [← F.map_comp, hab, F.map_id]
  have : Mono (F.map a) := mono_of_mono_fac hF
  have h₁ : IsZero ((homologyFunctor (A := ℤ) ℤ n).obj
        ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q Λ ν) ((reflectOne Q Λ hQ hρ).obj N)).obj
          (DG.DerivedCategory.Q.obj
            ((degreeZeroModuleFunctor (TensorProductAlgebra k Q Λ ν)).obj M)))) :=
    IsZero.of_mono (F.map a) hN
  -- The first argument, by the coefficient retract.
  let ra := (reflectOne Q Λ hQ hρ).map a
  let rb := (reflectOne Q Λ hQ hρ).map b
  refine isZero_derivedTensorHomology_coefficient_retract
    (M₁ := (reflectOne Q Λ hQ hρ).obj M) (M₂ := (reflectOne Q Λ hQ hρ).obj N)
    ra.hom.toAddMonoidHom.toIntLinearMap (fun c m => ra.hom.map_smul (op c) m)
    rb.hom.toAddMonoidHom.toIntLinearMap (fun c m => rb.hom.map_smul (op c) m) ?_ M n h₁
  refine LinearMap.ext fun m => ?_
  change (ra ≫ rb).hom m = m
  rw [← Functor.map_comp, hab, CategoryTheory.Functor.map_id]
  rfl

local notation "Cyc" => CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j)

/-- **No higher Tor on the diagonal** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22, gap (c), step R5, the diagonal `E²` term): for Rouquier `Q`, a summand `Y₀` of
`R^{λ_ℓ} e(u)` (`π ∘ ι = id`) and `M = S(T^{λ'} e(t) ⊠ Y₀)`, `Tor_n(M^r, M) = 0` for `n ≠ 0`.
The ordered standard covers `D` of the left standards are a hypothesis. -/
theorem isZero_derivedTensorHomology_reflectOne_tensorStd_of_ne_zero
    {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
    (D : OrderedStandardCovers
      (fun s : {s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s} =>
        ModuleCat.of (TensorProductAlgebra k Q Λ ν) (leftStandard Q Λ s.1 s.2))
      (fun s => seqIdem Q Λ s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    (u : List I) (h₀ : 0 + wordWt u 0 = ν) (t : Seq (stendhalWeight ℓ 0)) (ht : IsRedOrdered t)
    (Y₀ : ModuleCat.{0} (Cyc (wordWt u 0)))
    (ι : Y₀ →ₗ[Cyc (wordWt u 0)] cycWord Q Λ u) (π : cycWord Q Λ u →ₗ[Cyc (wordWt u 0)] Y₀)
    (hπι : π.comp ι = LinearMap.id) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor (A := ℤ) ℤ n).obj
      ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q Λ ν)
        ((reflectOne Q Λ hQ hρ).obj (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀))).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (TensorProductAlgebra k Q Λ ν)).obj
          (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀))))) := by
  obtain ⟨e⟩ := nonempty_cycWord_equiv_cycProj Q Λ u
  let X := oldProj Q Λ 0 t ht
  let a := ModuleCat.ofHom (tensorStdMapRight Q Λ hQ h₀ X (e.toLinearMap.comp ι))
  let b := ModuleCat.ofHom (tensorStdMapRight Q Λ hQ h₀ X (π.comp e.symm.toLinearMap))
  have hab : a ≫ b = 𝟙 _ := by
    refine ModuleCat.hom_ext ?_
    change (tensorStdMapRight Q Λ hQ h₀ X (π.comp e.symm.toLinearMap)).comp
      (tensorStdMapRight Q Λ hQ h₀ X (e.toLinearMap.comp ι)) = LinearMap.id
    rw [← tensorStdMapRight_comp]
    have : (π.comp e.symm.toLinearMap).comp (e.toLinearMap.comp ι) = LinearMap.id := by
      refine LinearMap.ext fun y => ?_
      change π (e.symm (e (ι y))) = y
      rw [LinearEquiv.symm_apply_apply]
      exact LinearMap.congr_fun hπι y
    rw [this, tensorStdMapRight_id]
  refine isZero_derivedTensorHomology_reflectOne_retract Q Λ hQ hρ a b hab n ?_
  have hold : HasStandardFiltrations Q (Λ ∘ Fin.castSucc) := by
    convert hasStandardFiltrations_of_rouquier hR hQ (Λ ∘ Fin.castSucc)
  obtain ⟨m', hm'⟩ := hold 0 t ht
  exact isZero_derivedTensorHomology_stdLayer_tensorProj_of_ne_zero Q Λ hQ hρ D hold h₀ ht _
    (hasFiltration_tensorReflect_one hQ hρ (hasFiltration_stdLayer_tensorProj Q Λ hQ h₀ ht _ hm'))
    n hn

end Categorification.Stendhal
