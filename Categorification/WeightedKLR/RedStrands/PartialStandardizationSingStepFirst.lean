/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSingSplit

/-!
# The standardization in stages, split at a cut: the first half of the inductive step

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3 (proof of
Lemma 7.19, where the standardization with singleton blocks is computed in stages). In the
inductive step from `r` to `r + 1` red strands in the second block, the standardization of all
`j + r + 1` red strands is the partial standardization at the cut before the last red strand of
the standardization of the first `j + r` red strands, with the last block in the spectator. By
the induction hypothesis, the latter is the partial standardization at the cut after the `j`-th
red strand of the standardizations of the two blocks (`singStepFirst`). That module is the input
of the one-step associativity `spectAssocAddEquiv`, for the module `singStepN` over the three
blocks.

## Main definitions

* `Stendhal.cutLastEquiv`, `Stendhal.cutLastCast`: the partial standardization at the cut before
  the last red strand of an intertwining isomorphism, along the identity and along a cast of
  weights.
* `Stendhal.spectAssocLeftInv`: the inverse of `spectAssocLeftAlg`.
* `Stendhal.singStepN`: the module over the three blocks of the inductive step.
* `Stendhal.singStepFirst`: the identification of the first stage of the inductive step.

## Main results

* `Stendhal.singStepFirst_smul`: it intertwines the actions along the cast of weights.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra TypeA
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I k : Type u} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q)

/-- Two casts of weights compose. -/
theorem castTensorProductAlgebra_comp {m : ℕ} (Λ : Fin m → I →₀ ℕ) {ν₁ ν₂ ν₃ : Multiset I}
    (h₁ : ν₁ = ν₂) (h₂ : ν₂ = ν₃) (t : TensorProductAlgebra k Q Λ ν₁) :
    castTensorProductAlgebra Q Λ h₂ (castTensorProductAlgebra Q Λ h₁ t) =
      castTensorProductAlgebra Q Λ (h₁.trans h₂) t := by
  subst h₁ h₂
  rfl

/-- The tensor product of two identities is the identity. -/
theorem tensorMap_id_id_apply {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (x : A ⊗[k] B) : Algebra.TensorProduct.map (AlgHom.id k A) (AlgHom.id k B) x = x :=
  DFunLike.congr_fun Algebra.TensorProduct.map_id x

/-- The spectator `T^R(γ) ⊗ E` of the last red strand and `E`. -/
def cutLastSpect (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (γ : Multiset I) (E : AlgCat.{u} k) :
    AlgCat.{u} k :=
  AlgCat.of k (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd n) γ ⊗[k] E)

/-- The associator `(T^A ⊗ T^R) ⊗ E → T^A ⊗ (T^R ⊗ E)` at the cut before the last red
strand. -/
def cutLastAssoc (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (w γ : Multiset I) (E : AlgCat.{u} k) :
    cutSpectAlgebra (a := n) (r := 1) Q Λ w γ E →+*
      TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) w ⊗[k]
        cutLastSpect Q n Λ γ E :=
  (Algebra.TensorProduct.assoc k k k (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) w)
    (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd n) γ) E).toAlgHom.toRingHom

/-- A module over `T^A ⊗ (T^R ⊗ E)` as a module for the cut before the last red strand. -/
abbrev cutLastObj (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (w γ : Multiset I) (E : AlgCat.{u} k)
    (X : ModuleCat.{u} (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) w ⊗[k]
      cutLastSpect Q n Λ γ E)) :
    ModuleCat.{u} (cutSpectAlgebra (a := n) (r := 1) Q Λ w γ E) :=
  (ModuleCat.restrictScalars.{u} (cutLastAssoc Q n Λ w γ E)).obj X

/-- Partial standardization at the cut before the last red strand of an intertwining
isomorphism along a map that is pointwise the identity. -/
def cutLastEquiv {n : ℕ} (Λ : Fin (n + 1) → I →₀ ℕ) (w γ : Multiset I) (E : AlgCat.{u} k)
    {X Y : ModuleCat.{u} (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) w ⊗[k]
      cutLastSpect Q n Λ γ E)}
    (e : X ≃+ Y) (he : ∀ (x : TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) w ⊗[k]
      cutLastSpect Q n Λ γ E)
      (m : X), e (x • m) = x • e m) :
    (cutSpectFunctor (a := n) (r := 1) Q Λ w γ E hQ).obj
        (cutLastObj Q n Λ w γ E X) ≃+
      (cutSpectFunctor (a := n) (r := 1) Q Λ w γ E hQ).obj
        (cutLastObj Q n Λ w γ E Y) :=
  cutSpectStandardEquivOf (a := n) (r := 1) Q Λ w γ (AlgHom.id k E)
    (N := cutLastObj Q n Λ w γ E X)
    (N' := cutLastObj Q n Λ w γ E Y) e
    (fun x m => (he _ m).trans (congrArg (fun z => cutLastAssoc Q n Λ w γ E z • e m)
      (tensorMap_id_id_apply (k := k) x).symm)) hQ

/-- `cutLastEquiv` intertwines the actions. -/
theorem cutLastEquiv_smul {n : ℕ} (Λ : Fin (n + 1) → I →₀ ℕ) (w γ : Multiset I)
    (E : AlgCat.{u} k)
    {X Y : ModuleCat.{u} (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) w ⊗[k]
      cutLastSpect Q n Λ γ E)}
    (e : X ≃+ Y) (he : ∀ (x : TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) w ⊗[k]
      cutLastSpect Q n Λ γ E)
      (m : X), e (x • m) = x • e m)
    (x : TensorProductAlgebra k Q Λ (w + γ) ⊗[k] E)
    (z : (cutSpectFunctor (a := n) (r := 1) Q Λ w γ E hQ).obj (cutLastObj Q n Λ w γ E X)) :
    cutLastEquiv Q hQ Λ w γ E e he (x • z) = x • cutLastEquiv Q hQ Λ w γ E e he z :=
  (cutSpectStandardEquivOf_smul (a := n) (r := 1) Q Λ w γ (AlgHom.id k E) _ _ hQ x z).trans
    (congrArg (· • cutLastEquiv Q hQ Λ w γ E e he z) (tensorMap_id_id_apply (k := k) x))

/-- **Partial standardization at the cut before the last red strand of an isomorphism along a
cast of weights**, intertwining the actions along the induced cast of weights. -/
def cutLastCast {n : ℕ} (Λ : Fin (n + 1) → I →₀ ℕ) {w w' : Multiset I} (h : w = w')
    (γ : Multiset I) (E : AlgCat.{u} k)
    {X : ModuleCat.{u} (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) w ⊗[k]
      cutLastSpect Q n Λ γ E)}
    {Y : ModuleCat.{u} (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) w' ⊗[k]
      cutLastSpect Q n Λ γ E)}
    (e : X ≃+ Y) (he : ∀ (x : TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) w ⊗[k]
      cutLastSpect Q n Λ γ E)
      (m : X), e (x • m) = Algebra.TensorProduct.map
        (castTensorProductAlgebra Q (Λ ∘ Fin.castSucc) h).toAlgHom (AlgHom.id k _) x • e m) :
    IntertwiningEquiv (Algebra.TensorProduct.map
        (castTensorProductAlgebra Q Λ (congrArg (· + γ) h)).toAlgHom (AlgHom.id k E)).toRingHom
      ((cutSpectFunctor (a := n) (r := 1) Q Λ w γ E hQ).obj (cutLastObj Q n Λ w γ E X))
      ((cutSpectFunctor (a := n) (r := 1) Q Λ w' γ E hQ).obj (cutLastObj Q n Λ w' γ E Y)) := by
  subst h
  exact
    { equiv := cutLastEquiv Q hQ Λ w γ E e
        (fun x m => (he x m).trans (congrArg (· • e m) (tensorMap_id_id_apply (k := k) x)))
      map_smul := fun x z => (cutLastEquiv_smul Q hQ Λ w γ E e _ x z).trans
        (congrArg (· • _) (tensorMap_id_id_apply (k := k) x).symm) }

section AssocInv

variable {a m : ℕ} (Λ : Fin (a + (m + 1)) → I →₀ ℕ) (θ β γ : Multiset I) (E : AlgCat.{u} k)

/-- The inverse of `spectAssocLeftAlg`. -/
def spectAssocLeftInv : blocksSpectAlgebra Q Λ θ β γ E →ₐ[k]
    cutSpectAlgebra (a := a) (r := m) Q (blocksLeftLabels (a := a) (m := m) (r := 1)
      (Λ ∘ Fin.cast (Nat.add_assoc a m 1))) θ β
      (AlgCat.of k (blocksLastAlgebra (a := a) (m := m) (r := 1) Q
        (Λ ∘ Fin.cast (Nat.add_assoc a m 1)) γ ⊗[k] E) : AlgCat.{u} k) :=
  (Algebra.TensorProduct.assoc k k k (cutFactorAlgebra Q (blocksLeftLabels (a := a) (m := m)
      (r := 1) (Λ ∘ Fin.cast (Nat.add_assoc a m 1))) θ β)
    (blocksLastAlgebra (a := a) (m := m) (r := 1) Q (Λ ∘ Fin.cast (Nat.add_assoc a m 1)) γ)
    E).toAlgHom.comp
    (Algebra.TensorProduct.map
      ((blocksAssocFactorEquiv (a := a) (m := m) (r := 1) Q Λ θ β γ).symm.toAlgHom :
        blocksTotalAlgebra Q Λ θ β γ →ₐ[k] _)
      (AlgHom.id k E))

/-- `spectAssocLeftInv` is a left inverse of `spectAssocLeftAlg`. -/
theorem spectAssocLeftInv_left (x : cutSpectAlgebra (a := a) (r := m) Q
    (blocksLeftLabels (a := a) (m := m) (r := 1) (Λ ∘ Fin.cast (Nat.add_assoc a m 1))) θ β
      (AlgCat.of k (blocksLastAlgebra (a := a) (m := m) (r := 1) Q
        (Λ ∘ Fin.cast (Nat.add_assoc a m 1)) γ ⊗[k] E) : AlgCat.{u} k)) :
    spectAssocLeftInv Q Λ θ β γ E (spectAssocLeftAlg Q Λ θ β γ E x) = x :=
  (congrArg (Algebra.TensorProduct.assoc k k k _ _ E)
    ((Algebra.TensorProduct.congr (blocksAssocFactorEquiv (a := a) (m := m) (r := 1) Q Λ θ β γ)
      (AlgEquiv.refl : E ≃ₐ[k] E)).symm_apply_apply _)).trans
    ((Algebra.TensorProduct.assoc k k k _ _ E).apply_symm_apply x)

end AssocInv

section Step

variable (j r : ℕ) (Λ : Fin (j + (r + 1)) → I →₀ ℕ) (θ : Fin (j + (r + 1)) → Multiset I)
  (E : AlgCat.{u} k)
  (Z : ModuleCat.{u} (singAlg Q j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1)) ⊗[k]
    (AlgCat.of k (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) :
      AlgCat.{u} k)))

local notation "Λc" => Λ ∘ Fin.castSucc
local notation "θc" => θ ∘ Fin.castSucc
local notation "Es" => cutLastSpect Q (j + r) Λ (θ (Fin.last (j + r))) E

/-- The module of the inductive step, with the last red strand moved into the spectator. -/
abbrev singStepZ : ModuleCat.{u} (singAlg Q j (Λc ∘ Fin.castAdd r) (θc ∘ Fin.castAdd r) ⊗[k]
    (AlgCat.of k (singAlg Q r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j) ⊗[k] Es) :
      AlgCat.{u} k)) :=
  (ModuleCat.restrictScalars.{u} (Algebra.TensorProduct.map
    (AlgHom.id k (singAlg Q j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1))))
    (singHeadMap Q j r Λ θ E)).toRingHom).obj Z

/-- The input of the standardization of the first `j + r` red strands, in the inductive step. -/
abbrev singStepA : ModuleCat.{u} (singAlg Q (j + r) Λc θc ⊗[k] Es) :=
  (ModuleCat.restrictScalars.{u} (singAssocIn Q (j + r) Λ θ E)).obj
    ((ModuleCat.restrictScalars.{u} (singSplit Q j (r + 1) Λ θ E).toRingHom).obj Z)

/-- The two inputs of the standardization of the first `j + r` red strands agree. -/
def singStepInSpect : SpectatorEquiv (singAlg Q (j + r) Λc θc) (AlgHom.id k Es)
    (singStepA Q j r Λ θ E Z)
    ((ModuleCat.restrictScalars.{u} (singSplit Q j r Λc θc Es).toRingHom).obj
      (singStepZ Q j r Λ θ E Z)) where
  equiv := AddEquiv.refl _
  map_smul x m := congrArg (fun z => Algebra.TensorProduct.map
      (AlgHom.id k (singAlg Q j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1))))
      (singHeadMap Q j r Λ θ E) (singSplit Q j r Λc θc Es z) • (show Z from m))
    (((Algebra.TensorProduct.assoc k k k _ (singLast Q Λ θ) E).apply_symm_apply x).trans
      (tensorMap_id_id_apply (k := k) x).symm)

local notation "θ0" => singWeight j (θc ∘ Fin.castAdd r)
local notation "βs" => singWeight r (θc ∘ Fin.natAdd j)
local notation "γs" => θ (Fin.last (j + r))

/-- The standardizations of the two blocks of the first `j + r` red strands, in the step. -/
abbrev singStepOuter : ModuleCat.{u} (cutSpectAlgebra (a := j) (r := r) Q Λc θ0 βs Es) :=
  (singOuter Q hQ j r Λc θc Es).obj (singStepZ Q j r Λ θ E Z)

/-- `spectAssocLeftInv` in the labels of the standardization in stages. -/
def singStepLeftInv : blocksSpectAlgebra Q Λ θ0 βs γs E →ₐ[k]
    cutSpectAlgebra (a := j) (r := r) Q Λc θ0 βs Es := spectAssocLeftInv Q Λ θ0 βs γs E

/-- `spectAssocLeftAlg` in the labels of the standardization in stages. -/
def singStepLeftAlg : cutSpectAlgebra (a := j) (r := r) Q Λc θ0 βs Es →ₐ[k]
    blocksSpectAlgebra Q Λ θ0 βs γs E := spectAssocLeftAlg Q Λ θ0 βs γs E

/-- `singStepLeftInv` is a left inverse of `singStepLeftAlg`. -/
theorem singStepLeftInv_left (x : cutSpectAlgebra (a := j) (r := r) Q Λc θ0 βs Es) :
    singStepLeftInv Q j r Λ θ E (singStepLeftAlg Q j r Λ θ E x) = x :=
  spectAssocLeftInv_left Q Λ θ0 βs γs E x

/-- The module over the three blocks of the inductive step. -/
abbrev singStepN : ModuleCat.{u} (blocksSpectAlgebra Q Λ θ0 βs γs E) :=
  (ModuleCat.restrictScalars.{u} (singStepLeftInv Q j r Λ θ E).toRingHom).obj
    (singStepOuter Q hQ j r Λ θ E Z)

/-- `spectLeftInput` in the labels of the standardization in stages. -/
abbrev singStepLeftIn : ModuleCat.{u} (cutSpectAlgebra (a := j) (r := r) Q Λc θ0 βs Es) :=
  (ModuleCat.restrictScalars.{u} (singStepLeftAlg Q j r Λ θ E).toRingHom).obj
    (singStepN Q hQ j r Λ θ E Z)

/-- The action on `singStepLeftIn` is the action on `singStepOuter`. -/
theorem singStepLeftIn_smul (x : cutSpectAlgebra (a := j) (r := r) Q Λc θ0 βs Es)
    (m : singStepOuter Q hQ j r Λ θ E Z) :
    (x • (show singStepLeftIn Q hQ j r Λ θ E Z from m) : singStepLeftIn Q hQ j r Λ θ E Z) =
      (x • m : singStepOuter Q hQ j r Λ θ E Z) :=
  congrArg (· • m) (singStepLeftInv_left Q j r Λ θ E x)

/-- The partial standardization at the first cut of the step agrees with that of
`spectLeftInput`. -/
def singStepLeftInput :
    (cutSpectFunctor (a := j) (r := r) Q Λc θ0 βs Es hQ).obj (singStepOuter Q hQ j r Λ θ E Z) ≃+
      (cutSpectFunctor (a := j) (r := r) Q Λc θ0 βs Es hQ).obj
        (singStepLeftIn Q hQ j r Λ θ E Z) :=
  cutSpectStandardEquivOf (a := j) (r := r) Q Λc θ0 βs (AlgHom.id k Es)
    (N := singStepOuter Q hQ j r Λ θ E Z)
    (N' := singStepLeftIn Q hQ j r Λ θ E Z) (AddEquiv.refl _)
    (fun x m => (singStepLeftIn_smul Q hQ j r Λ θ E Z x m).symm.trans
      (congrArg (· • (show singStepLeftIn Q hQ j r Λ θ E Z from m))
        (tensorMap_id_id_apply (k := k) x).symm)) hQ

/-- The standardization of the first `j + r` red strands in the step, from the induction
hypothesis. -/
abbrev singStepX : ModuleCat.{u} (TensorProductAlgebra k Q Λc (singWeight (j + r) θc) ⊗[k] Es) :=
  (singStd Q hQ (j + r) Λc θc Es).obj (singStepA Q j r Λ θ E Z)

/-- The partial standardization at the first cut, in the step. -/
abbrev singStepY : ModuleCat.{u} (TensorProductAlgebra k Q Λc (θ0 + βs) ⊗[k] Es) :=
  (cutSpectFunctor (a := j) (r := r) Q Λc θ0 βs Es hQ).obj (singStepLeftIn Q hQ j r Λ θ E Z)

variable {Q hQ j r Λ θ E Z} in
/-- From the induction hypothesis to the partial standardization at the first cut. -/
def singStepFirst
    (ih : IntertwiningEquiv (singWeightCast Q j r Λc θc Es).toRingHom
      ((singStd Q hQ (j + r) Λc θc Es).obj
        ((ModuleCat.restrictScalars.{u} (singSplit Q j r Λc θc Es).toRingHom).obj
          (singStepZ Q j r Λ θ E Z)))
      ((cutSpectFunctor (a := j) (r := r) Q Λc θ0 βs Es hQ).obj
        (singStepOuter Q hQ j r Λ θ E Z))) :
    singStepX Q hQ j r Λ θ E Z ≃+ singStepY Q hQ j r Λ θ E Z :=
  ((singStdSpectatorEquiv Q hQ (j + r) Λc θc (AlgHom.id k Es)
    (singStepInSpect Q j r Λ θ E Z)).equiv.trans ih.equiv).trans
    (singStepLeftInput Q hQ j r Λ θ E Z)

variable {Q hQ j r Λ θ E Z} in
/-- `singStepFirst` intertwines the actions along the cast of weights. -/
theorem singStepFirst_smul
    (ih : IntertwiningEquiv (singWeightCast Q j r Λc θc Es).toRingHom
      ((singStd Q hQ (j + r) Λc θc Es).obj
        ((ModuleCat.restrictScalars.{u} (singSplit Q j r Λc θc Es).toRingHom).obj
          (singStepZ Q j r Λ θ E Z)))
      ((cutSpectFunctor (a := j) (r := r) Q Λc θ0 βs Es hQ).obj
        (singStepOuter Q hQ j r Λ θ E Z)))
    (x : TensorProductAlgebra k Q Λc (singWeight (j + r) θc) ⊗[k] Es)
    (m : singStepX Q hQ j r Λ θ E Z) :
    singStepFirst ih (x • m) = singWeightCast Q j r Λc θc Es x • singStepFirst ih m :=
  (congrArg (fun z => singStepLeftInput Q hQ j r Λ θ E Z (ih.equiv z))
    ((singStdSpectatorEquiv Q hQ (j + r) Λc θc (AlgHom.id k Es)
      (singStepInSpect Q j r Λ θ E Z)).map_smul x m)).trans
  ((congrArg (singStepLeftInput Q hQ j r Λ θ E Z) (ih.map_smul _ _)).trans
  ((cutSpectStandardEquivOf_smul (a := j) (r := r) Q Λc θ0 βs (AlgHom.id k Es) _ _ hQ _ _).trans
    (congrArg (· • singStepFirst ih m) ((tensorMap_id_id_apply (k := k) _).trans
      (congrArg (singWeightCast Q j r Λc θc Es) (tensorMap_id_id_apply (k := k) x))))))

end Step

end Categorification.Stendhal
