/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveStdSumPairs
import Categorification.Algebra.ShortComplexCoefficientSyzygyChain

/-!
# Dévissage of the S-move Tor along the resolutions of Proposition 7.8

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c), with dévissage in place of the spectral sequence. Let `L` be a
module over `T^{λ_2, λ_3}(ν)` and `L'` a module over `T^{λ_1, λ_2}(ν)`, each resolved as in
Proposition 7.8 (`exists_stdResolution`, two red strands): chains of short exact sequences
`0 → K_{n+1} → M_n → K_n → 0`, `K_0 ≅ L`, whose middle terms `M_n` are sums of standard layers
at position `|ν| + 1 - n` (`StdSum`) and vanish for `n > |ν|`. Applying the exact functors
`(SMove.leftStd −)^r` and `SMove.rightStd` gives resolutions of `(SMove.leftStd L)^r` and of
`SMove.rightStd L'` over `T^λ(ν)`. Every pair of terms except `(0, |ν|)` is Tor-acyclic
(`SMove.torAcyclic_reflect_leftStd_rightStd_stdSum_of_ne`), so by
`nonempty_linearEquiv_derivedTensorHomology_of_syzygyChains`

`H^n((SMove.leftStd L)^r ⊗ᴸ SMove.rightStd L') ≅ H^{n + |ν|}((SMove.leftStd M_0)^r ⊗ᴸ
SMove.rightStd M'_{|ν|})`,

and if the diagonal pair has no higher Tor, the left side is concentrated in degree `-|ν|`.

Route hypotheses: a Rouquier choice of `Q` (`IsRouquierQ`), and, for the concentration, the
vanishing of the higher Tor of the diagonal pair `((SMove.leftStd M_0)^r, SMove.rightStd
M'_{|ν|})` (`hdiag`), which is step R5 of the write-up and is not proved here. Tor is over `ℤ`
(the coefficient ring of the Tor lemmas of the S-move); the identifications are of
`ℤ`-modules.

## Main results

* `SMove.nonempty_linearEquiv_derivedTensorHomology_reflect_leftStd_rightStd`: the shift to the
  diagonal pair.
* `SMove.nonempty_linearEquiv_derivedTensorHomology_reflect_leftStd_rightStd_neg`: the degree
  `-|ν|` term is `Tor₀` of the diagonal pair.
* `SMove.isZero_derivedTensorHomology_reflect_leftStd_rightStd_of_ne`: concentration in degree
  `-|ν|`, given the diagonal hypothesis.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.SMove

open CategoryTheory CategoryTheory.Limits KLR ModuleFiltration Equiv BraidedStendhalAlgebra
open DG DG.DerivedCategory
open scoped TensorProduct DG.DegreeZero

universe w

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

omit [HasDerivedCategory.{w, 0}
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (ν := ν)
      (List.map (1 : Perm (Fin (1 + 1 + 1))) (List.finRange (1 + 1 + 1))))]
  [HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν)]
  [HasDerivedCategory.{w, 0} ℤ] in
/-- `(SMove.leftStd −)^r` is exact. -/
theorem moduleExactFunctor_leftStd_reflectOne :
    ModuleExactFunctor (leftStd Q hQ Λ ν ⋙
      reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ) :=
  (moduleExactFunctor_leftStd Q hQ Λ ν).comp (ModuleExactFunctor.restrictScalars _)

variable {L : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) ν)}
  {L' : ModuleCat.{0} (TensorProductAlgebra k Q
    ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc) ν)}
  (S : ℕ → ShortComplex (ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) ν)))
  (h0 : Nonempty ((S 0).X₃ ≅ L)) (hs : ∀ n, Nonempty ((S (n + 1)).X₃ ≅ (S n).X₁))
  (hS : ∀ n, (S n).ShortExact)
  (hstd : ∀ n ≤ Multiset.card ν,
    StdSum Q (Λ ∘ Fin.natAdd 1) hQ (Multiset.card ν + 1 - n) (S n).X₂)
  (hz : ∀ n, Multiset.card ν < n → IsZero (S n).X₂)
  (S' : ℕ → ShortComplex (ModuleCat.{0} (TensorProductAlgebra k Q
    ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc) ν)))
  (h0' : Nonempty ((S' 0).X₃ ≅ L')) (hs' : ∀ n, Nonempty ((S' (n + 1)).X₃ ≅ (S' n).X₁))
  (hS' : ∀ n, (S' n).ShortExact)
  (hstd' : ∀ n ≤ Multiset.card ν,
    StdSum Q ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc) hQ
      (Multiset.card ν + 1 - n) (S' n).X₂)
  (hz' : ∀ n, Multiset.card ν < n → IsZero (S' n).X₂)

include hρ h0 hs hS hstd hz h0' hs' hS' hstd' hz' in
/-- **The S-move Tor is the Tor of the diagonal pair, shifted by `|ν|`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, gap (c), dévissage in place of the spectral
sequence): for Rouquier `Q` and resolutions of `L` and `L'` as in Proposition 7.8 on two red
strands,
`H^n((SMove.leftStd L)^r ⊗ᴸ SMove.rightStd L') ≅
  H^{n + |ν|}((SMove.leftStd M_0)^r ⊗ᴸ SMove.rightStd M'_{|ν|})` over `ℤ`. -/
theorem nonempty_linearEquiv_derivedTensorHomology_reflect_leftStd_rightStd
    {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q) (n : ℤ) :
    Nonempty ((homologyFunctor (A := ℤ) ℤ n).obj
        ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν)
          ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ).obj
            ((leftStd Q hQ Λ ν).obj L))).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
            ((rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν).obj L')))) ≃ₗ[ℤ]
      (homologyFunctor (A := ℤ) ℤ (n + Multiset.card ν)).obj
        ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν)
          ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ).obj
            ((leftStd Q hQ Λ ν).obj (S 0).X₂))).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
            ((rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν).obj
              (S' (Multiset.card ν)).X₂))))) := by
  have hF := moduleExactFunctor_leftStd_reflectOne Q hQ Λ hρ
  have hG := moduleExactFunctor_rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν
  let F := leftStd Q hQ Λ ν ⋙ reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ
  let G := rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν
  obtain ⟨cX, hlen, hterm, hsyz⟩ := CoefficientSyzygyChain.exists_of_rightShortComplexes
    (fun m => exactMapShortComplex hF (S m) (hS m)) (h0.map F.mapIso)
    (fun m => (hs m).map F.mapIso) (fun m => exactMapShortComplex_shortExact hF (S m) (hS m))
    (Multiset.card ν) fun m hm => by
      have := ModuleCat.isZero_iff_subsingleton.mp (hz m hm)
      exact ModuleCat.isZero_iff_subsingleton.mpr (subsingleton_obj_of_subsingleton hF _)
  obtain ⟨cY, hlen', hterm', ⟨hsyz'⟩⟩ := ModuleSyzygyChain.exists_of_shortComplexes
    (fun m => exactMapShortComplex hG (S' m) (hS' m)) (h0'.map G.mapIso)
    (fun m => (hs' m).map G.mapIso) (fun m => exactMapShortComplex_shortExact hG (S' m) (hS' m))
    (Multiset.card ν) fun m hm => by
      have := ModuleCat.isZero_iff_subsingleton.mp (hz' m hm)
      exact ModuleCat.isZero_iff_subsingleton.mpr (subsingleton_obj_of_subsingleton hG _)
  obtain ⟨e⟩ := nonempty_linearEquiv_derivedTensorHomology_of_syzygyChains.{w} cX cY
    (i₀ := 0) (j₀ := Multiset.card ν) (Nat.zero_le _) hlen'.ge (fun i hi j hj hij m => by
      rw [hlen] at hi
      rw [hlen'] at hj
      rw [hterm i, hterm' j]
      exact (torAcyclic_reflect_leftStd_rightStd_stdSum_of_ne.{w} Q hQ Λ hρ hR
          (hij.imp_right fun h => lt_of_le_of_ne hj h) (hstd i hi) (hstd' j hj) m).of_iso
        (coefficientOfRightHomologyEquiv.{w} _ _ m).toModuleIso) n
  have hdeg : n + ((0 : ℕ) : ℤ) + ((Multiset.card ν : ℕ) : ℤ) = n + Multiset.card ν := by
    rw [Nat.cast_zero, add_zero]
  rw [hdeg] at e
  exact ⟨((homologyFunctor (A := ℤ) ℤ n).mapIso ((derivedTensor.{w} ℤ _ _).mapIso
    (DG.DerivedCategory.Q.mapIso ((degreeZeroModuleFunctor _).mapIso
      hsyz')))).toLinearEquiv.symm.trans
        ((coefficientOfRightHomologyEquivOfEq.{w} hsyz _ n).symm.trans
        (e.trans ((coefficientOfRightHomologyEquivOfEq.{w} (hterm 0) _ _).trans
          ((homologyFunctor (A := ℤ) ℤ _).mapIso ((derivedTensor.{w} ℤ _ _).mapIso
            (DG.DerivedCategory.Q.mapIso ((degreeZeroModuleFunctor _).mapIso
              (eqToIso (hterm' (Multiset.card ν))))))).toLinearEquiv)))⟩

include hρ h0 hs hS hstd hz h0' hs' hS' hstd' hz' in
/-- **The S-move Tor in degree `-|ν|` is `Tor₀` of the diagonal pair** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, gap (c)): under the hypotheses of
`nonempty_linearEquiv_derivedTensorHomology_reflect_leftStd_rightStd`,
`H^{-|ν|}((SMove.leftStd L)^r ⊗ᴸ SMove.rightStd L') ≅
  H^0((SMove.leftStd M_0)^r ⊗ᴸ SMove.rightStd M'_{|ν|})` over `ℤ`. -/
theorem nonempty_linearEquiv_derivedTensorHomology_reflect_leftStd_rightStd_neg
    {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q) :
    Nonempty ((homologyFunctor (A := ℤ) ℤ (-(Multiset.card ν : ℤ))).obj
        ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν)
          ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ).obj
            ((leftStd Q hQ Λ ν).obj L))).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
            ((rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν).obj L')))) ≃ₗ[ℤ]
      (homologyFunctor (A := ℤ) ℤ 0).obj
        ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν)
          ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ).obj
            ((leftStd Q hQ Λ ν).obj (S 0).X₂))).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
            ((rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν).obj
              (S' (Multiset.card ν)).X₂))))) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_derivedTensorHomology_reflect_leftStd_rightStd.{w} Q hQ Λ
    hρ S h0 hs hS hstd hz S' h0' hs' hS' hstd' hz' hR (-(Multiset.card ν : ℤ))
  exact ⟨e.trans (eqToIso (congrArg (fun d : ℤ => (homologyFunctor (A := ℤ) ℤ d).obj _)
    (neg_add_cancel (Multiset.card ν : ℤ)))).toLinearEquiv⟩

include hρ h0 hs hS hstd hz h0' hs' hS' hstd' hz' in
/-- **Concentration of the S-move Tor in degree `-|ν|`** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.22, gap (c)): under the hypotheses of
`nonempty_linearEquiv_derivedTensorHomology_reflect_leftStd_rightStd`, if the diagonal pair
`((SMove.leftStd M_0)^r, SMove.rightStd M'_{|ν|})` has no higher Tor (`hdiag`, route
hypothesis: step R5 of the diagonal term, not proved here), then
`H^n((SMove.leftStd L)^r ⊗ᴸ SMove.rightStd L') = 0` for `n ≠ -|ν|`. -/
theorem isZero_derivedTensorHomology_reflect_leftStd_rightStd_of_ne
    {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
    (hdiag : ∀ m : ℤ, m ≠ 0 → IsZero ((homologyFunctor (A := ℤ) ℤ m).obj
        ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν)
          ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ).obj
            ((leftStd Q hQ Λ ν).obj (S 0).X₂))).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
            ((rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν).obj
              (S' (Multiset.card ν)).X₂))))))
    (n : ℤ) (hn : n ≠ -(Multiset.card ν : ℤ)) :
    IsZero ((homologyFunctor (A := ℤ) ℤ n).obj
        ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν)
          ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ).obj
            ((leftStd Q hQ Λ ν).obj L))).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
            ((rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν).obj L'))))) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_derivedTensorHomology_reflect_leftStd_rightStd.{w} Q hQ Λ
    hρ S h0 hs hS hstd hz S' h0' hs' hS' hstd' hz' hR n
  exact (hdiag _ (by omega)).of_iso e.toModuleIso

end Categorification.Stendhal.SMove
