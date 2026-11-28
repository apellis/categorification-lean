/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSingCut
import Categorification.WeightedKLR.RedStrands.PartialStandardizationNatural

/-!
# Naturality of the standardization split at a cut

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, toward
the derived form of Lemma 7.19 (K): the comparison `singCutEquiv` of the standardization of all
red strands with the partial standardization at a cut of the standardizations of the two blocks
is natural in the module.

## Main results

* `Stendhal.cutSpectTransport_natural`: naturality of `cutSpectTransport`.
-/

set_option backward.isDefEq.respectTransparency false

universe u

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra TypeA
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I k : Type u} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q)

section Transport

variable {a r : ℕ} {Λ Λ' : Fin (a + r) → I →₀ ℕ} (hΛ : Λ = Λ') {θ θ' β β' : Multiset I}
  (hθ : θ = θ') (hβ : β = β') {E E' : AlgCat.{u} k} (φ : E →ₐ[k] E')
  {N M : ModuleCat.{u} (cutSpectAlgebra Q Λ θ β E)}
  {N' M' : ModuleCat.{u} (cutSpectAlgebra Q Λ' θ' β' E')}

/-- **The transported partial standardization is natural.** -/
theorem cutSpectTransport_natural (f : N ≃+ N')
    (hf : ∀ (x : cutSpectAlgebra Q Λ θ β E) (n : N),
      f (x • n) = cutSpectRecast Q hΛ hθ hβ φ x • f n) (f₂ : M ≃+ M')
    (hf₂ : ∀ (x : cutSpectAlgebra Q Λ θ β E) (n : M),
      f₂ (x • n) = cutSpectRecast Q hΛ hθ hβ φ x • f₂ n) (g : N ⟶ M) (g' : N' ⟶ M')
    (h : ∀ n, f₂ (g.hom n) = g'.hom (f n)) (z : (cutSpectFunctor Q Λ θ β E hQ).obj N) :
    (cutSpectTransport Q hQ hΛ hθ hβ φ f₂ hf₂).equiv
        (((cutSpectFunctor Q Λ θ β E hQ).map g).hom z) =
      ((cutSpectFunctor Q Λ' θ' β' E' hQ).map g').hom
        ((cutSpectTransport Q hQ hΛ hθ hβ φ f hf).equiv z) := by
  subst hΛ hθ hβ
  exact cutStandardMap_square Q Λ θ β _ _ _ _ h z

end Transport

section Zero

variable (j : ℕ) (Λ : Fin (j + 0) → I →₀ ℕ) (θ : Fin (j + 0) → Multiset I) (E : AlgCat.{u} k)
  {Z W : ModuleCat.{u} (singAlg Q j (Λ ∘ Fin.castAdd 0) (θ ∘ Fin.castAdd 0) ⊗[k]
    (AlgCat.of k (singAlg Q 0 (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) : AlgCat.{u} k))}

/-- The trivial change of spectator inside `singZeroSpect`. -/
def singZeroInSpect (Z : ModuleCat.{u} (singAlg Q j (Λ ∘ Fin.castAdd 0) (θ ∘ Fin.castAdd 0) ⊗[k]
    (AlgCat.of k (singAlg Q 0 (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) : AlgCat.{u} k))) :
    SpectatorEquiv (singAlg Q j (Λ ∘ Fin.castAdd 0) (θ ∘ Fin.castAdd 0))
      (Algebra.TensorProduct.includeRight : E →ₐ[k]
        (AlgCat.of k (singAlg Q 0 (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) : AlgCat.{u} k))
      ((ModuleCat.restrictScalars.{u} (singSplit Q j 0 Λ θ E).toRingHom).obj Z) Z :=
  ⟨AddEquiv.refl _, fun _ _ => rfl⟩

/-- The base case of `singCutEquiv` is natural. -/
theorem singCutEquivZero_natural (g : Z ⟶ W)
    (x : (singStd Q hQ (j + 0) Λ θ E).obj
      ((ModuleCat.restrictScalars.{u} (singSplit Q j 0 Λ θ E).toRingHom).obj Z)) :
    (singCutEquivZero Q hQ j Λ θ E W).equiv
        (((ModuleCat.restrictScalars.{u} (singSplit Q j 0 Λ θ E).toRingHom ⋙
          singStd Q hQ (j + 0) Λ θ E).map g).hom x) =
      ((singOuter Q hQ j 0 Λ θ E ⋙ cutSpectFunctor (a := j) (r := 0) Q Λ _ _ E hQ).map g).hom
        ((singCutEquivZero Q hQ j Λ θ E Z).equiv x) :=
by
  have h1 := singStdSpectatorEquiv_natural Q hQ j (Λ ∘ Fin.castAdd 0) (θ ∘ Fin.castAdd 0)
      (Algebra.TensorProduct.includeRight : E →ₐ[k]
        (AlgCat.of k (singAlg Q 0 (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) : AlgCat.{u} k))
      (Z := (ModuleCat.restrictScalars.{u} (singSplit Q j 0 Λ θ E).toRingHom).obj Z)
      (W := (ModuleCat.restrictScalars.{u} (singSplit Q j 0 Λ θ E).toRingHom).obj W)
      (Z' := Z) (W' := W) (singZeroInSpect Q j Λ θ E Z) (singZeroInSpect Q j Λ θ E W)
      ((ModuleCat.restrictScalars.{u} (singSplit Q j 0 Λ θ E).toRingHom).map g) g
      (fun _ => rfl) x
  exact congrArg (cutStandardUnit (a := j) (r := 0) Q Λ _ (singWeight 0 (θ ∘ Fin.natAdd j))
      (singZeroInput Q hQ j Λ θ E W)) h1

end Zero

section Step

variable (j r : ℕ) (Λ : Fin (j + (r + 1)) → I →₀ ℕ) (θ : Fin (j + (r + 1)) → Multiset I)
  (E : AlgCat.{u} k)
  {Z W : ModuleCat.{u} (singAlg Q j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1)) ⊗[k]
    (AlgCat.of k (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) :
      AlgCat.{u} k))}

local notation "Λc" => Λ ∘ Fin.castSucc
local notation "θc" => θ ∘ Fin.castSucc
local notation "Es" => cutLastSpect Q (j + r) Λ (θ (Fin.last (j + r))) E
local notation "θ0" => singWeight j (θc ∘ Fin.castAdd r)
local notation "βs" => singWeight r (θc ∘ Fin.natAdd j)
local notation "γs" => θ (Fin.last (j + r))

/-- `singStepZ` on maps. -/
abbrev singStepZFunctor :
    ModuleCat.{u} (singAlg Q j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1)) ⊗[k]
      (AlgCat.of k (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) :
        AlgCat.{u} k)) ⥤
    ModuleCat.{u} (singAlg Q j (Λc ∘ Fin.castAdd r) (θc ∘ Fin.castAdd r) ⊗[k]
      (AlgCat.of k (singAlg Q r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j) ⊗[k] Es) :
        AlgCat.{u} k)) :=
  ModuleCat.restrictScalars.{u} (Algebra.TensorProduct.map
    (AlgHom.id k (singAlg Q j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1))))
    (singHeadMap Q j r Λ θ E)).toRingHom

set_option hygiene false in
local notation "Hd" => TensorProductAlgebra k Q (Λ ∘ Fin.castAdd (r + 1))
  (singWeight j (θ ∘ Fin.castAdd (r + 1)))
set_option hygiene false in
local notation "SH" => singStd Q hQ j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1))
  (AlgCat.of k (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E))
set_option hygiene false in
local notation "SH'" => singStd Q hQ j (Λc ∘ Fin.castAdd r) (θc ∘ Fin.castAdd r)
  (AlgCat.of k (singAlg Q r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j) ⊗[k] Es))

/-- `singTailV` on maps. -/
abbrev singTailVFunctor :
    ModuleCat.{u} (singAlg Q j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1)) ⊗[k]
      (AlgCat.of k (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) :
        AlgCat.{u} k)) ⥤
    ModuleCat.{u} (singAlg Q r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j) ⊗[k]
      (AlgCat.of k (TensorProductAlgebra k Q (Λc ∘ Fin.castAdd r) θ0 ⊗[k] Es) : AlgCat.{u} k)) :=
  singStepZFunctor Q j r Λ θ E ⋙ SH' ⋙
    ModuleCat.restrictScalars.{u} (Algebra.TensorProduct.leftComm k
      (singAlg Q r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j))
      (TensorProductAlgebra k Q (Λc ∘ Fin.castAdd r) θ0) Es).toAlgHom.toRingHom

/-- `singTailW₀` on maps. -/
abbrev singTailW₀Functor :
    ModuleCat.{u} (singAlg Q j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1)) ⊗[k]
      (AlgCat.of k (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) :
        AlgCat.{u} k)) ⥤
    ModuleCat.{u} (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k]
      singTailHE Q j r Λ θ E) :=
  SH ⋙ ModuleCat.restrictScalars.{u} (singTailLeftComm Q j r Λ θ E)

/-- `singTailW` on maps. -/
abbrev singTailWFunctor :
    ModuleCat.{u} (singAlg Q j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1)) ⊗[k]
      (AlgCat.of k (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) :
        AlgCat.{u} k)) ⥤
    ModuleCat.{u} (singAlg Q r ((Λ ∘ Fin.natAdd j) ∘ Fin.castSucc)
      ((θ ∘ Fin.natAdd j) ∘ Fin.castSucc) ⊗[k] singTailTgt Q j r Λ θ E) :=
  singTailW₀Functor Q hQ j r Λ θ E ⋙ ModuleCat.restrictScalars.{u}
    (singAssocIn Q r (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) (singTailHE Q j r Λ θ E))

/-- The trivial change of spectator inside `singTailHead`. -/
def singTailHeadIn
    (Z : ModuleCat.{u} (singAlg Q j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1)) ⊗[k]
      (AlgCat.of k (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) :
        AlgCat.{u} k))) :
    SpectatorEquiv (singAlg Q j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1)))
      (singTailHeadMap Q j r Λ θ E) (singStepZ Q j r Λ θ E Z) Z :=
  ⟨AddEquiv.refl _, fun _ _ => rfl⟩

/-- `singStepN` on maps. -/
abbrev singStepNFunctor :
    ModuleCat.{u} (singAlg Q j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1)) ⊗[k]
      (AlgCat.of k (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) :
        AlgCat.{u} k)) ⥤
    ModuleCat.{u} (blocksSpectAlgebra Q Λ θ0 βs γs E) :=
  singStepZFunctor Q j r Λ θ E ⋙ singOuter Q hQ j r Λc θc Es ⋙
    ModuleCat.restrictScalars.{u} (singStepLeftInv Q j r Λ θ E).toRingHom

/-- `singTailInner` on maps. -/
abbrev singTailInnerFunctor :
    ModuleCat.{u} (singAlg Q j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1)) ⊗[k]
      (AlgCat.of k (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) :
        AlgCat.{u} k)) ⥤
    ModuleCat.{u} (cutSpectAlgebra (a := r) (r := 1) Q (Λ ∘ Fin.natAdd j)
      (singWeight r ((θ ∘ Fin.natAdd j) ∘ Fin.castSucc)) ((θ ∘ Fin.natAdd j) (Fin.last r))
      (singTailHE Q j r Λ θ E)) :=
  singTailWFunctor Q hQ j r Λ θ E ⋙
    singStd Q hQ r ((Λ ∘ Fin.natAdd j) ∘ Fin.castSucc) ((θ ∘ Fin.natAdd j) ∘ Fin.castSucc)
      (singTailTgt Q j r Λ θ E) ⋙
    ModuleCat.restrictScalars.{u} (singAssocOut Q r (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)
      (singTailHE Q j r Λ θ E))

/-- `singStepZ` on maps. -/
def singStepZMap (g : Z ⟶ W) : singStepZ Q j r Λ θ E Z ⟶ singStepZ Q j r Λ θ E W :=
  (singStepZFunctor Q j r Λ θ E).map g

/-- `singTailV` on maps. -/
def singTailVMap (g : Z ⟶ W) : singTailV Q hQ j r Λ θ E Z ⟶ singTailV Q hQ j r Λ θ E W :=
  (singTailVFunctor Q hQ j r Λ θ E).map g

/-- `singTailW` on maps. -/
def singTailWMap (g : Z ⟶ W) : singTailW Q hQ j r Λ θ E Z ⟶ singTailW Q hQ j r Λ θ E W :=
  (singTailWFunctor Q hQ j r Λ θ E).map g

/-- `singStepN` on maps. -/
def singStepNMap (g : Z ⟶ W) : singStepN Q hQ j r Λ θ E Z ⟶ singStepN Q hQ j r Λ θ E W :=
  (singStepNFunctor Q hQ j r Λ θ E).map g

/-- `singTailInner` on maps. -/
def singTailInnerMap (g : Z ⟶ W) :
    singTailInner Q hQ j r Λ θ E Z ⟶ singTailInner Q hQ j r Λ θ E W :=
  (singTailInnerFunctor Q hQ j r Λ θ E).map g

/-- `singTailHead` is natural. -/
theorem singTailHead_natural (g : Z ⟶ W) (x : (SH').obj (singStepZ Q j r Λ θ E Z)) :
    (singTailHead Q hQ j r Λ θ E W).equiv
        (((SH').map (singStepZMap Q j r Λ θ E g)).hom x) =
      ((SH).map g).hom ((singTailHead Q hQ j r Λ θ E Z).equiv x) :=
  singStdSpectatorEquiv_natural Q hQ j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1))
    (singTailHeadMap Q j r Λ θ E) (singTailHeadIn Q j r Λ θ E Z) (singTailHeadIn Q j r Λ θ E W)
    (singStepZMap Q j r Λ θ E g) g (fun _ => rfl) x

/-- `singTailSecond` is natural. -/
theorem singTailSecond_natural (g : Z ⟶ W)
    (x : (singStd Q hQ r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j)
      (AlgCat.of k (TensorProductAlgebra k Q (Λc ∘ Fin.castAdd r) θ0 ⊗[k] Es))).obj
        (singTailV Q hQ j r Λ θ E Z)) :
    (singTailSecond Q hQ j r Λ θ E W).equiv
        (((singStd Q hQ r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j)
          (AlgCat.of k (TensorProductAlgebra k Q (Λc ∘ Fin.castAdd r) θ0 ⊗[k] Es))).map
            (singTailVMap Q hQ j r Λ θ E g)).hom x) =
      ((singStd Q hQ r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j) (singTailTgt Q j r Λ θ E)).map
          (singTailWMap Q hQ j r Λ θ E g)).hom
        ((singTailSecond Q hQ j r Λ θ E Z).equiv x) :=
  singStdSpectatorEquiv_natural Q hQ r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j)
    (singTailPsi Q j r Λ θ E) (singTailMid Q hQ j r Λ θ E Z) (singTailMid Q hQ j r Λ θ E W)
    (singTailVMap Q hQ j r Λ θ E g) (singTailWMap Q hQ j r Λ θ E g)
    (singTailHead_natural Q hQ j r Λ θ E g) x

set_option hygiene false in
local notation "H0" => TensorProductAlgebra k Q (Λ ∘ Fin.castAdd (r + 1)) θ0

theorem singStepNMap_hom (g : Z ⟶ W)
    (n : spectRightInput Q Λ θ0 βs γs E (singStepN Q hQ j r Λ θ E Z)) :
    ((ModuleCat.restrictScalars.{u} (spectAssocRightAlg Q Λ θ0 βs γs E).toRingHom).map
      (singStepNMap Q hQ j r Λ θ E g)).hom n =
    ((singStd Q hQ r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j)
          (AlgCat.of k (TensorProductAlgebra k Q (Λc ∘ Fin.castAdd r) θ0 ⊗[k] Es))).map
            (singTailVMap Q hQ j r Λ θ E g)).hom n := rfl

theorem singTailInnerMap_hom (g : Z ⟶ W)
    (n : (singStd Q hQ r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j) (singTailTgt Q j r Λ θ E)).obj
      (singTailW Q hQ j r Λ θ E Z)) :
    (singTailInnerMap Q hQ j r Λ θ E g).hom n =
      ((singStd Q hQ r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j) (singTailTgt Q j r Λ θ E)).map
          (singTailWMap Q hQ j r Λ θ E g)).hom n := rfl

/-- `singTailThird` is natural. -/
theorem singTailThird_natural (g : Z ⟶ W)
    (z : (cutSpectFunctor (a := r) (r := 1) Q (Λ ∘ Fin.natAdd j) βs γs
      (AlgCat.of k (H0 ⊗[k] E)) hQ).obj
        (spectRightInput Q Λ θ0 βs γs E (singStepN Q hQ j r Λ θ E Z))) :
    (singTailThird Q hQ j r Λ θ E W).equiv
        (((cutSpectFunctor (a := r) (r := 1) Q (Λ ∘ Fin.natAdd j) βs γs
          (AlgCat.of k (H0 ⊗[k] E)) hQ).map
            ((ModuleCat.restrictScalars.{u} (spectAssocRightAlg Q Λ θ0 βs γs E).toRingHom).map
              (singStepNMap Q hQ j r Λ θ E g))).hom z) =
      ((cutSpectFunctor (a := r) (r := 1) Q (Λ ∘ Fin.natAdd j)
          (singWeight r ((θ ∘ Fin.natAdd j) ∘ Fin.castSucc)) ((θ ∘ Fin.natAdd j) (Fin.last r))
          (singTailHE Q j r Λ θ E) hQ).map (singTailInnerMap Q hQ j r Λ θ E g)).hom
        ((singTailThird Q hQ j r Λ θ E Z).equiv z) := by
  let gN₀ := (ModuleCat.restrictScalars.{u} (spectAssocRightAlg Q Λ θ0 βs γs E).toRingHom).map
      (singStepNMap Q hQ j r Λ θ E g)
  let gN : spectRightInput Q Λ θ0 βs γs E (singStepN Q hQ j r Λ θ E Z) ⟶
      spectRightInput Q Λ θ0 βs γs E (singStepN Q hQ j r Λ θ E W) := gN₀
  let gN'₀ := (singTailInnerFunctor Q hQ j r Λ θ E).map g
  let gN' : singTailInner Q hQ j r Λ θ E Z ⟶ singTailInner Q hQ j r Λ θ E W := gN'₀
  have hS : ∀ n, (singTailSecond Q hQ j r Λ θ E W).equiv (gN.hom n) =
        gN'.hom ((singTailSecond Q hQ j r Λ θ E Z).equiv n) :=
    fun n => (congrArg (singTailSecond Q hQ j r Λ θ E W).equiv
      (singStepNMap_hom Q hQ j r Λ θ E g n)).trans
      ((singTailSecond_natural Q hQ j r Λ θ E g n).trans
        (singTailInnerMap_hom Q hQ j r Λ θ E g _).symm)
  have hT := cutSpectTransport_natural Q hQ (a := r) (r := 1) (Λ := Λ ∘ Fin.natAdd j)
    (Λ' := Λ ∘ Fin.natAdd j) (θ := βs) (θ' := singWeight r ((θ ∘ Fin.natAdd j) ∘ Fin.castSucc))
    (β := γs) (β' := (θ ∘ Fin.natAdd j) (Fin.last r)) rfl
    (rfl : βs = singWeight r ((θ ∘ Fin.natAdd j) ∘ Fin.castSucc))
    (rfl : γs = (θ ∘ Fin.natAdd j) (Fin.last r)) (singTailSpectId Q j r Λ θ E)
    (N := spectRightInput Q Λ θ0 βs γs E (singStepN Q hQ j r Λ θ E Z))
    (M := spectRightInput Q Λ θ0 βs γs E (singStepN Q hQ j r Λ θ E W))
    (N' := singTailInner Q hQ j r Λ θ E Z) (M' := singTailInner Q hQ j r Λ θ E W)
    (singTailSecond Q hQ j r Λ θ E Z).equiv
    (fun x n => ((singTailSecond Q hQ j r Λ θ E Z).map_smul
      (singRotOut Q j r Λc θ0 βs Es (singStepLeftInv Q j r Λ θ E
        (spectAssocRightAlg Q Λ θ0 βs γs E x))) n).trans
      (congrArg (· • (singTailSecond Q hQ j r Λ θ E Z).equiv n)
        (singTailInner_apply Q j r Λ θ E x)))
    (singTailSecond Q hQ j r Λ θ E W).equiv
    (fun x n => ((singTailSecond Q hQ j r Λ θ E W).map_smul
      (singRotOut Q j r Λc θ0 βs Es (singStepLeftInv Q j r Λ θ E
        (spectAssocRightAlg Q Λ θ0 βs γs E x))) n).trans
      (congrArg (· • (singTailSecond Q hQ j r Λ θ E W).equiv n)
        (singTailInner_apply Q j r Λ θ E x)))
    gN gN' hS z
  exact hT

/-- `singTailW₀` on maps. -/
def singTailW₀Map (g : Z ⟶ W) : singTailW₀ Q hQ j r Λ θ E Z ⟶ singTailW₀ Q hQ j r Λ θ E W :=
  (singTailW₀Functor Q hQ j r Λ θ E).map g

/-- The rotation of the first stage of `singOuter` at `r + 1`, as a functor. -/
abbrev singTailLCFunctor :
    ModuleCat.{u} (singAlg Q j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1)) ⊗[k]
      (AlgCat.of k (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) :
        AlgCat.{u} k)) ⥤
    ModuleCat.{u} (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k]
      (AlgCat.of k (Hd ⊗[k] E) : AlgCat.{u} k)) :=
  SH ⋙ ModuleCat.restrictScalars.{u} (Algebra.TensorProduct.leftComm k
    (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)) Hd E).toAlgHom.toRingHom

/-- The rotation of the first stage of `singOuter` at `r + 1`, on maps. -/
def singTailLCMap (g : Z ⟶ W) :
    (ModuleCat.restrictScalars.{u} (Algebra.TensorProduct.leftComm k
        (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)) Hd E).toAlgHom.toRingHom).obj
      ((SH).obj Z) ⟶
    (ModuleCat.restrictScalars.{u} (Algebra.TensorProduct.leftComm k
        (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)) Hd E).toAlgHom.toRingHom).obj
      ((SH).obj W) :=
  (singTailLCFunctor Q hQ j r Λ θ E).map g

/-- `singTailCross` is natural. -/
theorem singTailCross_natural (g : Z ⟶ W)
    (z : (cutSpectFunctor (a := r) (r := 1) Q (Λ ∘ Fin.natAdd j)
      (singWeight r ((θ ∘ Fin.natAdd j) ∘ Fin.castSucc)) ((θ ∘ Fin.natAdd j) (Fin.last r))
      (singTailHE Q j r Λ θ E) hQ).obj (singTailInner Q hQ j r Λ θ E Z)) :
    (singTailCross Q hQ j r Λ θ E W).equiv
        (((cutSpectFunctor (a := r) (r := 1) Q (Λ ∘ Fin.natAdd j)
          (singWeight r ((θ ∘ Fin.natAdd j) ∘ Fin.castSucc)) ((θ ∘ Fin.natAdd j) (Fin.last r))
          (singTailHE Q j r Λ θ E) hQ).map (singTailInnerMap Q hQ j r Λ θ E g)).hom z) =
      ((singStd Q hQ (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) (singTailHE Q j r Λ θ E)).map
          (singTailW₀Map Q hQ j r Λ θ E g)).hom ((singTailCross Q hQ j r Λ θ E Z).equiv z) :=
  rfl

/-- The trivial change of spectator inside `singTailFourth`. -/
def singTailFourthIn
    (Z : ModuleCat.{u} (singAlg Q j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1)) ⊗[k]
      (AlgCat.of k (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) :
        AlgCat.{u} k))) :
    SpectatorEquiv (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j))
      (singTailSpectBack Q j r Λ θ E) (singTailW₀ Q hQ j r Λ θ E Z)
      ((ModuleCat.restrictScalars.{u} (Algebra.TensorProduct.leftComm k
        (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)) Hd E).toAlgHom.toRingHom).obj
          ((SH).obj Z)) :=
  ⟨AddEquiv.refl _, fun x m => congrArg (fun y => singTailLeftComm Q j r Λ θ E y •
    (show (SH).obj Z from m)) (tensorMap_id_id_apply (k := k) x).symm⟩

/-- `singTailFourth` is natural. -/
theorem singTailFourth_natural (g : Z ⟶ W)
    (x : (singStd Q hQ (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)
      (singTailHE Q j r Λ θ E)).obj (singTailW₀ Q hQ j r Λ θ E Z)) :
    (singTailFourth Q hQ j r Λ θ E W).equiv
        (((singStd Q hQ (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)
          (singTailHE Q j r Λ θ E)).map (singTailW₀Map Q hQ j r Λ θ E g)).hom x) =
      ((singStd Q hQ (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)
          (AlgCat.of k (Hd ⊗[k] E))).map (singTailLCMap Q hQ j r Λ θ E g)).hom
        ((singTailFourth Q hQ j r Λ θ E Z).equiv x) :=
  singStdSpectatorEquiv_natural Q hQ (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)
    (singTailSpectBack Q j r Λ θ E) (singTailFourthIn Q hQ j r Λ θ E Z)
    (singTailFourthIn Q hQ j r Λ θ E W) (singTailW₀Map Q hQ j r Λ θ E g)
    (singTailLCMap Q hQ j r Λ θ E g) (fun _ => rfl) x

set_option hygiene false in
local notation "NNZ" => (ModuleCat.restrictScalars.{u} (spectHeadAlg Q Λ θ0 βs γs E).toRingHom).obj
      ((cutSpectFunctor (a := r) (r := 1) Q (Λ ∘ Fin.natAdd j) βs γs
          (AlgCat.of k (H0 ⊗[k] E)) hQ).obj
        (spectRightInput Q Λ θ0 βs γs E (singStepN Q hQ j r Λ θ E Z)))

/-- The input map of the tail chain. -/
abbrev singTailChainIn (g : Z ⟶ W) :=
  (ModuleCat.restrictScalars.{u} (spectHeadAlg Q Λ θ0 βs γs E).toRingHom).map
    ((cutSpectFunctor (a := r) (r := 1) Q (Λ ∘ Fin.natAdd j) βs γs
        (AlgCat.of k (H0 ⊗[k] E)) hQ).map
      ((ModuleCat.restrictScalars.{u} (spectAssocRightAlg Q Λ θ0 βs γs E).toRingHom).map
        (singStepNMap Q hQ j r Λ θ E g)))

theorem singTailChain_equiv (z : NNZ) :
    (singTailChain Q hQ j r Λ θ E Z).equiv z =
      (singTailFourth Q hQ j r Λ θ E Z).equiv ((singTailCross Q hQ j r Λ θ E Z).equiv
        ((singTailThird Q hQ j r Λ θ E Z).equiv z)) := rfl

theorem singTailChainIn_hom (g : Z ⟶ W) (z : NNZ) :
    (singTailChainIn Q hQ j r Λ θ E g).hom z =
      ((cutSpectFunctor (a := r) (r := 1) Q (Λ ∘ Fin.natAdd j) βs γs
        (AlgCat.of k (H0 ⊗[k] E)) hQ).map
          ((ModuleCat.restrictScalars.{u} (spectAssocRightAlg Q Λ θ0 βs γs E).toRingHom).map
            (singStepNMap Q hQ j r Λ θ E g))).hom z := rfl

theorem singOuter_map_hom (g : Z ⟶ W)
    (x : (singStd Q hQ (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)
      (AlgCat.of k (Hd ⊗[k] E))).obj
        ((ModuleCat.restrictScalars.{u} (Algebra.TensorProduct.leftComm k
          (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)) Hd E).toAlgHom.toRingHom).obj
            ((SH).obj Z))) :
    ((singStd Q hQ (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)
        (AlgCat.of k (Hd ⊗[k] E))).map (singTailLCMap Q hQ j r Λ θ E g)).hom x =
      ((singOuter Q hQ j (r + 1) Λ θ E).map g).hom x := rfl

/-- `singTailChain` is natural. -/
theorem singTailChain_natural (g : Z ⟶ W) (z : NNZ) :
    (singTailChain Q hQ j r Λ θ E W).equiv ((singTailChainIn Q hQ j r Λ θ E g).hom z) =
      ((singOuter Q hQ j (r + 1) Λ θ E).map g).hom ((singTailChain Q hQ j r Λ θ E Z).equiv z) :=
  (singTailChain_equiv Q hQ j r Λ θ E _).trans
    ((congrArg (fun y => (singTailFourth Q hQ j r Λ θ E W).equiv
        ((singTailCross Q hQ j r Λ θ E W).equiv ((singTailThird Q hQ j r Λ θ E W).equiv y)))
      (singTailChainIn_hom Q hQ j r Λ θ E g z)).trans
    ((congrArg (fun y => (singTailFourth Q hQ j r Λ θ E W).equiv
        ((singTailCross Q hQ j r Λ θ E W).equiv y))
      (singTailThird_natural Q hQ j r Λ θ E g z)).trans
    ((congrArg (singTailFourth Q hQ j r Λ θ E W).equiv
        (singTailCross_natural Q hQ j r Λ θ E g _)).trans
    ((singTailFourth_natural Q hQ j r Λ θ E g _).trans
    ((singOuter_map_hom Q hQ j r Λ θ E g _).trans
      (congrArg ((singOuter Q hQ j (r + 1) Λ θ E).map g).hom
        (singTailChain_equiv Q hQ j r Λ θ E z).symm))))))

/-- `singStepTail` is natural. -/
theorem singStepTail_natural (g : Z ⟶ W)
    (z : (cutSpectFunctor (a := j) (r := r + 1) Q Λ θ0 (βs + γs) E hQ).obj NNZ) :
    (singStepTail Q hQ j r Λ θ E W).equiv
        (((cutSpectFunctor (a := j) (r := r + 1) Q Λ θ0 (βs + γs) E hQ).map
          (singTailChainIn Q hQ j r Λ θ E g)).hom z) =
      ((cutSpectFunctor (a := j) (r := r + 1) Q Λ (singWeight j (θ ∘ Fin.castAdd (r + 1)))
          (singWeight (r + 1) (θ ∘ Fin.natAdd j)) E hQ).map
            ((singOuter Q hQ j (r + 1) Λ θ E).map g)).hom
        ((singStepTail Q hQ j r Λ θ E Z).equiv z) := by
  have hT := cutSpectTransport_natural Q hQ (a := j) (r := r + 1) (Λ := Λ) (Λ' := Λ)
    (θ := θ0) (θ' := singWeight j (θ ∘ Fin.castAdd (r + 1))) (β := βs + γs)
    (β' := singWeight (r + 1) (θ ∘ Fin.natAdd j)) rfl rfl rfl (AlgHom.id k E)
    (N := NNZ) (M := (ModuleCat.restrictScalars.{u} (spectHeadAlg Q Λ θ0 βs γs E).toRingHom).obj
      ((cutSpectFunctor (a := r) (r := 1) Q (Λ ∘ Fin.natAdd j) βs γs
          (AlgCat.of k (H0 ⊗[k] E)) hQ).obj
        (spectRightInput Q Λ θ0 βs γs E (singStepN Q hQ j r Λ θ E W))))
    (N' := (singOuter Q hQ j (r + 1) Λ θ E).obj Z) (M' := (singOuter Q hQ j (r + 1) Λ θ E).obj W)
    (singTailChain Q hQ j r Λ θ E Z).equiv (singTailChain_smul Q hQ j r Λ θ E Z)
    (singTailChain Q hQ j r Λ θ E W).equiv (singTailChain_smul Q hQ j r Λ θ E W)
    (singTailChainIn Q hQ j r Λ θ E g) ((singOuter Q hQ j (r + 1) Λ θ E).map g)
    (singTailChain_natural Q hQ j r Λ θ E g) z
  exact hT

end Step

end Categorification.Stendhal
