/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSingCutNatural
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSpectatorAssocNatural

/-!
# Naturality of the standardization split at a cut: the inductive step

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, toward
the derived form of Lemma 7.19 (K): the left side of the inductive step of `singCutEquiv` and
the one-step associativity are natural, hence so is `singCutEquiv`.

## Main results

* `Stendhal.singCutEquiv_natural`: naturality of `singCutEquiv` in the module.
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

namespace IntertwiningEquiv

variable {A A' A'' : Type*} [Ring A] [Ring A'] [Ring A''] {f : A →+* A'} {g : A' →+* A''}
  {M M' M'' N N' N'' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A' M']
  [AddCommGroup M''] [Module A'' M''] [AddCommGroup N] [Module A N] [AddCommGroup N']
  [Module A' N'] [AddCommGroup N''] [Module A'' N'']

/-- Naturality is preserved by composition of intertwining isomorphisms. -/
theorem trans_natural {e₁ : IntertwiningEquiv f M M'} {e₁' : IntertwiningEquiv f N N'}
    {e₂ : IntertwiningEquiv g M' M''} {e₂' : IntertwiningEquiv g N' N''}
    {a : M → N} {b : M' → N'} {c : M'' → N''}
    (h₁ : ∀ x, e₁'.equiv (a x) = b (e₁.equiv x)) (h₂ : ∀ y, e₂'.equiv (b y) = c (e₂.equiv y)) :
    ∀ x, (e₁'.trans e₂').equiv (a x) = c ((e₁.trans e₂).equiv x) :=
  fun x => (congrArg e₂'.equiv (h₁ x)).trans (h₂ _)

/-- Naturality is preserved by `ofEq`. -/
theorem ofEq_natural {e : IntertwiningEquiv f M M'} {e' : IntertwiningEquiv f N N'}
    {f' : A →+* A'} {hM : ∀ x, f x = f' x} {hN : ∀ x, f x = f' x} {a : M → N} {b : M' → N'}
    (h : ∀ x, e'.equiv (a x) = b (e.equiv x)) :
    ∀ x, (e'.ofEq hN).equiv (a x) = b ((e.ofEq hM).equiv x) := h

end IntertwiningEquiv

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

/-- `singStepA` as a functor. -/
abbrev singStepAFunctor :
    ModuleCat.{u} (singAlg Q j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1)) ⊗[k]
      (AlgCat.of k (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) :
        AlgCat.{u} k)) ⥤ ModuleCat.{u} (singAlg Q (j + r) Λc θc ⊗[k] Es) :=
  ModuleCat.restrictScalars.{u} (singSplit Q j (r + 1) Λ θ E).toRingHom ⋙
    ModuleCat.restrictScalars.{u} (singAssocIn Q (j + r) Λ θ E)

/-- `singStepA` on maps. -/
def singStepAMap (g : Z ⟶ W) : singStepA Q j r Λ θ E Z ⟶ singStepA Q j r Λ θ E W :=
  (singStepAFunctor Q j r Λ θ E).map g

/-- `singStepLeftIn` as a functor. -/
abbrev singStepLeftInFunctor :
    ModuleCat.{u} (blocksSpectAlgebra Q Λ θ0 βs γs E) ⥤
      ModuleCat.{u} (cutSpectAlgebra (a := j) (r := r) Q Λc θ0 βs Es) :=
  ModuleCat.restrictScalars.{u} (singStepLeftAlg Q j r Λ θ E).toRingHom

/-- `singStepLeftIn` on maps. -/
def singStepLeftInMap (g : Z ⟶ W) :
    singStepLeftIn Q hQ j r Λ θ E Z ⟶ singStepLeftIn Q hQ j r Λ θ E W :=
  (singStepLeftInFunctor Q j r Λ θ E).map (singStepNMap Q hQ j r Λ θ E g)

/-- `singStepOuter` on maps. -/
def singStepOuterMap (g : Z ⟶ W) :
    singStepOuter Q hQ j r Λ θ E Z ⟶ singStepOuter Q hQ j r Λ θ E W :=
  (singOuter Q hQ j r Λc θc Es).map (singStepZMap Q j r Λ θ E g)

theorem singStepInMap_hom (g : Z ⟶ W)
    (x : (singStd Q hQ (j + r) Λc θc Es).obj
      ((ModuleCat.restrictScalars.{u} (singSplit Q j r Λc θc Es).toRingHom).obj
        (singStepZ Q j r Λ θ E Z))) :
    ((singStd Q hQ (j + r) Λc θc Es).map
      ((ModuleCat.restrictScalars.{u} (singSplit Q j r Λc θc Es).toRingHom).map
        (singStepZMap Q j r Λ θ E g))).hom x =
    ((ModuleCat.restrictScalars.{u} (singSplit Q j r Λc θc Es).toRingHom ⋙
      singStd Q hQ (j + r) Λc θc Es).map (singStepZMap Q j r Λ θ E g)).hom x := rfl

theorem singStepOuterMap_hom (g : Z ⟶ W)
    (z : (cutSpectFunctor (a := j) (r := r) Q Λc θ0 βs Es hQ).obj
      (singStepOuter Q hQ j r Λ θ E Z)) :
    ((singOuter Q hQ j r Λc θc Es ⋙ cutSpectFunctor (a := j) (r := r) Q Λc θ0 βs Es hQ).map
      (singStepZMap Q j r Λ θ E g)).hom z =
    cutSpectStandardMap (a := j) (r := r) Q Λc θ0 βs hQ (singStepOuterMap Q hQ j r Λ θ E g).hom
      z := rfl

variable {Q hQ j r Λ θ E} in
/-- `singStepFirst` is natural, given the naturality of the induction hypothesis. -/
theorem singStepFirst_natural (g : Z ⟶ W)
    (ihZ : IntertwiningEquiv (singWeightCast Q j r Λc θc Es).toRingHom
      ((singStd Q hQ (j + r) Λc θc Es).obj
        ((ModuleCat.restrictScalars.{u} (singSplit Q j r Λc θc Es).toRingHom).obj
          (singStepZ Q j r Λ θ E Z)))
      ((cutSpectFunctor (a := j) (r := r) Q Λc θ0 βs Es hQ).obj
        (singStepOuter Q hQ j r Λ θ E Z)))
    (ihW : IntertwiningEquiv (singWeightCast Q j r Λc θc Es).toRingHom
      ((singStd Q hQ (j + r) Λc θc Es).obj
        ((ModuleCat.restrictScalars.{u} (singSplit Q j r Λc θc Es).toRingHom).obj
          (singStepZ Q j r Λ θ E W)))
      ((cutSpectFunctor (a := j) (r := r) Q Λc θ0 βs Es hQ).obj
        (singStepOuter Q hQ j r Λ θ E W)))
    (hih : ∀ x, ihW.equiv (((ModuleCat.restrictScalars.{u} (singSplit Q j r Λc θc Es).toRingHom ⋙
        singStd Q hQ (j + r) Λc θc Es).map (singStepZMap Q j r Λ θ E g)).hom x) =
      ((singOuter Q hQ j r Λc θc Es ⋙ cutSpectFunctor (a := j) (r := r) Q Λc θ0 βs Es hQ).map
        (singStepZMap Q j r Λ θ E g)).hom (ihZ.equiv x))
    (x : singStepX Q hQ j r Λ θ E Z) :
    singStepFirst ihW (((singStd Q hQ (j + r) Λc θc Es).map
        (singStepAMap Q j r Λ θ E g)).hom x) =
      cutSpectStandardMap (a := j) (r := r) Q Λc θ0 βs hQ
        (singStepLeftInMap Q hQ j r Λ θ E g).hom (singStepFirst ihZ x) := by
  have h1 := singStdSpectatorEquiv_natural Q hQ (j + r) Λc θc (AlgHom.id k Es)
    (singStepInSpect Q j r Λ θ E Z) (singStepInSpect Q j r Λ θ E W)
    (singStepAMap Q j r Λ θ E g)
    ((ModuleCat.restrictScalars.{u} (singSplit Q j r Λc θc Es).toRingHom).map
      (singStepZMap Q j r Λ θ E g)) (fun _ => rfl) x
  have h2 := (congrArg ihW.equiv h1).trans
    ((congrArg ihW.equiv (singStepInMap_hom Q hQ j r Λ θ E g _)).trans
      ((hih _).trans (singStepOuterMap_hom Q hQ j r Λ θ E g _)))
  have h3 := cutSpectStandardEquivOf_natural (a := j) (r := r) Q Λc θ0 βs (AlgHom.id k Es)
    (N := singStepOuter Q hQ j r Λ θ E Z) (N' := singStepLeftIn Q hQ j r Λ θ E Z)
    (M := singStepOuter Q hQ j r Λ θ E W) (M' := singStepLeftIn Q hQ j r Λ θ E W)
    (AddEquiv.refl _)
    (fun x m => (singStepLeftIn_smul Q hQ j r Λ θ E Z x m).symm.trans
      (congrArg (· • (show singStepLeftIn Q hQ j r Λ θ E Z from m))
        (tensorMap_id_id_apply (k := k) x).symm))
    (AddEquiv.refl _)
    (fun x m => (singStepLeftIn_smul Q hQ j r Λ θ E W x m).symm.trans
      (congrArg (· • (show singStepLeftIn Q hQ j r Λ θ E W from m))
        (tensorMap_id_id_apply (k := k) x).symm)) hQ
    (singStepOuterMap Q hQ j r Λ θ E g).hom (singStepLeftInMap Q hQ j r Λ θ E g).hom
    (fun _ => rfl) (ihZ.equiv ((singStdSpectatorEquiv Q hQ (j + r) Λc θc (AlgHom.id k Es)
      (singStepInSpect Q j r Λ θ E Z)).equiv x))
  exact (congrArg (singStepLeftInput Q hQ j r Λ θ E W) h2).trans h3

set_option hygiene false in
local notation "ΛA" => blocksLeftLabels (a := j) (m := r) (r := 1)
  (Λ ∘ Fin.cast (Nat.add_assoc j r 1))
set_option hygiene false in
local notation "EL" => (AlgCat.of k (blocksLastAlgebra (a := j) (m := r) (r := 1) Q
  (Λ ∘ Fin.cast (Nat.add_assoc j r 1)) γs ⊗[k] E) : AlgCat.{u} k)

/-- The map of the inputs at the first cut, in the form of the one-step associativity. -/
abbrev singStepSpectLeftMap (g : Z ⟶ W) :=
  (ModuleCat.restrictScalars.{u} (spectAssocLeftAlg Q Λ θ0 βs γs E).toRingHom).map
    (singStepNMap Q hQ j r Λ θ E g)

/-- `singStepCrossFirst` is natural. -/
theorem singStepCrossFirst_natural (g : Z ⟶ W)
    (z : (cutSpectFunctor (a := j) (r := r) Q Λc θ0 βs Es hQ).obj
      (singStepLeftIn Q hQ j r Λ θ E Z)) :
    (singStepCrossFirst Q hQ j r Λ θ E W).equiv
        (((cutSpectFunctor (a := j) (r := r) Q Λc θ0 βs Es hQ).map
          (singStepLeftInMap Q hQ j r Λ θ E g)).hom z) =
      ((cutSpectFunctor (a := j) (r := r) Q ΛA θ0 βs EL hQ).map
          (singStepSpectLeftMap Q hQ j r Λ θ E g)).hom
        ((singStepCrossFirst Q hQ j r Λ θ E Z).equiv z) := by
  have hT := cutSpectTransport_natural Q hQ (Λ := Λc) (Λ' := ΛA) (θ := θ0) (θ' := θ0)
    (β := βs) (β' := βs) rfl rfl rfl (singStepSpectId Q j r Λ θ E)
    (N := singStepLeftIn Q hQ j r Λ θ E Z) (M := singStepLeftIn Q hQ j r Λ θ E W)
    (N' := spectLeftInput Q Λ θ0 βs γs E (singStepN Q hQ j r Λ θ E Z))
    (M' := spectLeftInput Q Λ θ0 βs γs E (singStepN Q hQ j r Λ θ E W))
    (AddEquiv.refl _) (singStepCrossFirst_smul Q hQ j r Λ θ E Z)
    (AddEquiv.refl _) (singStepCrossFirst_smul Q hQ j r Λ θ E W)
    (singStepLeftInMap Q hQ j r Λ θ E g) (singStepSpectLeftMap Q hQ j r Λ θ E g)
    (fun _ => rfl) z
  exact hT

/-- `singStepX` on maps, at the last cut. -/
def singStepXMap (g : Z ⟶ W) :
    cutLastObj Q (j + r) Λ (singWeight (j + r) θc) γs E (singStepX Q hQ j r Λ θ E Z) ⟶
      cutLastObj Q (j + r) Λ (singWeight (j + r) θc) γs E (singStepX Q hQ j r Λ θ E W) :=
  (ModuleCat.restrictScalars.{u} (cutLastAssoc Q (j + r) Λ (singWeight (j + r) θc) γs E)).map
    ((singStd Q hQ (j + r) Λc θc Es).map (singStepAMap Q j r Λ θ E g))

/-- The input map of the left side of the one-step associativity. -/
abbrev singStepLastMap (g : Z ⟶ W) :=
  (ModuleCat.restrictScalars.{u} (spectLastAlg Q Λ θ0 βs γs E).toRingHom).map
    ((cutSpectFunctor (a := j) (r := r) Q ΛA θ0 βs EL hQ).map
      (singStepSpectLeftMap Q hQ j r Λ θ E g))

theorem singStepXMap_hom (g : Z ⟶ W)
    (x : cutLastObj Q (j + r) Λ (singWeight (j + r) θc) γs E (singStepX Q hQ j r Λ θ E Z)) :
    (singStepXMap Q hQ j r Λ θ E g).hom x =
      ((singStd Q hQ (j + r) Λc θc Es).map (singStepAMap Q j r Λ θ E g)).hom x := rfl

theorem singStepLeftInMap_hom (g : Z ⟶ W)
    (z : (cutSpectFunctor (a := j) (r := r) Q Λc θ0 βs Es hQ).obj
      (singStepLeftIn Q hQ j r Λ θ E Z)) :
    cutSpectStandardMap (a := j) (r := r) Q Λc θ0 βs hQ
        (singStepLeftInMap Q hQ j r Λ θ E g).hom z =
      ((cutSpectFunctor (a := j) (r := r) Q Λc θ0 βs Es hQ).map
          (singStepLeftInMap Q hQ j r Λ θ E g)).hom z := rfl

variable {Q hQ j r Λ θ E} in
/-- `singStepSecond` is natural, given the naturality of the induction hypothesis. -/
theorem singStepSecond_natural (g : Z ⟶ W)
    (ihZ : IntertwiningEquiv (singWeightCast Q j r Λc θc Es).toRingHom
      ((singStd Q hQ (j + r) Λc θc Es).obj
        ((ModuleCat.restrictScalars.{u} (singSplit Q j r Λc θc Es).toRingHom).obj
          (singStepZ Q j r Λ θ E Z)))
      ((cutSpectFunctor (a := j) (r := r) Q Λc θ0 βs Es hQ).obj
        (singStepOuter Q hQ j r Λ θ E Z)))
    (ihW : IntertwiningEquiv (singWeightCast Q j r Λc θc Es).toRingHom
      ((singStd Q hQ (j + r) Λc θc Es).obj
        ((ModuleCat.restrictScalars.{u} (singSplit Q j r Λc θc Es).toRingHom).obj
          (singStepZ Q j r Λ θ E W)))
      ((cutSpectFunctor (a := j) (r := r) Q Λc θ0 βs Es hQ).obj
        (singStepOuter Q hQ j r Λ θ E W)))
    (hih : ∀ x, ihW.equiv (((ModuleCat.restrictScalars.{u} (singSplit Q j r Λc θc Es).toRingHom ⋙
        singStd Q hQ (j + r) Λc θc Es).map (singStepZMap Q j r Λ θ E g)).hom x) =
      ((singOuter Q hQ j r Λc θc Es ⋙ cutSpectFunctor (a := j) (r := r) Q Λc θ0 βs Es hQ).map
        (singStepZMap Q j r Λ θ E g)).hom (ihZ.equiv x))
    (z : (cutSpectFunctor (a := j + r) (r := 1) Q Λ (singWeight (j + r) θc) γs E hQ).obj
      (cutLastObj Q (j + r) Λ (singWeight (j + r) θc) γs E (singStepX Q hQ j r Λ θ E Z))) :
    (singStepSecond ihW).equiv (((cutSpectFunctor (a := j + r) (r := 1) Q Λ
        (singWeight (j + r) θc) γs E hQ).map (singStepXMap Q hQ j r Λ θ E g)).hom z) =
      ((cutSpectFunctor (a := j + r) (r := 1) Q (Λ ∘ Fin.cast (Nat.add_assoc j r 1))
          (θ0 + βs) γs E hQ).map (singStepLastMap Q hQ j r Λ θ E g)).hom
        ((singStepSecond ihZ).equiv z) := by
  have hS : ∀ n, ((singStepFirst ihW).trans (singStepCrossFirst Q hQ j r Λ θ E W).equiv)
      ((singStepXMap Q hQ j r Λ θ E g).hom n) = (singStepLastMap Q hQ j r Λ θ E g).hom
        (((singStepFirst ihZ).trans (singStepCrossFirst Q hQ j r Λ θ E Z).equiv) n) :=
    fun n => (congrArg (singStepCrossFirst Q hQ j r Λ θ E W).equiv
      ((congrArg (singStepFirst ihW) (singStepXMap_hom Q hQ j r Λ θ E g n)).trans
        ((singStepFirst_natural g ihZ ihW hih n).trans
          (singStepLeftInMap_hom Q hQ j r Λ θ E g _)))).trans
      (singStepCrossFirst_natural Q hQ j r Λ θ E g _)
  have hT := cutSpectTransport_natural Q hQ (a := j + r) (r := 1) (Λ := Λ)
    (Λ' := Λ ∘ Fin.cast (Nat.add_assoc j r 1)) (θ := singWeight (j + r) θc) (θ' := θ0 + βs)
    (β := γs) (β' := γs) rfl (singWeight_add j r θc) rfl (AlgHom.id k E)
    (N := cutLastObj Q (j + r) Λ (singWeight (j + r) θc) γs E (singStepX Q hQ j r Λ θ E Z))
    (M := cutLastObj Q (j + r) Λ (singWeight (j + r) θc) γs E (singStepX Q hQ j r Λ θ E W))
    (N' := (ModuleCat.restrictScalars.{u} (spectLastAlg Q Λ θ0 βs γs E).toRingHom).obj
      ((cutSpectFunctor (a := j) (r := r) Q ΛA θ0 βs EL hQ).obj
        (spectLeftInput Q Λ θ0 βs γs E (singStepN Q hQ j r Λ θ E Z))))
    (M' := (ModuleCat.restrictScalars.{u} (spectLastAlg Q Λ θ0 βs γs E).toRingHom).obj
      ((cutSpectFunctor (a := j) (r := r) Q ΛA θ0 βs EL hQ).obj
        (spectLeftInput Q Λ θ0 βs γs E (singStepN Q hQ j r Λ θ E W))))
    ((singStepFirst ihZ).trans (singStepCrossFirst Q hQ j r Λ θ E Z).equiv)
    (fun x n => ((congrArg (singStepCrossFirst Q hQ j r Λ θ E Z).equiv
        (singStepFirst_smul ihZ _ n)).trans
      ((singStepCrossFirst Q hQ j r Λ θ E Z).map_smul _ _)).trans
      (congrArg (· • (singStepCrossFirst Q hQ j r Λ θ E Z).equiv (singStepFirst ihZ n))
        (singStepLast_apply Q j r Λ θ E x)))
    ((singStepFirst ihW).trans (singStepCrossFirst Q hQ j r Λ θ E W).equiv)
    (fun x n => ((congrArg (singStepCrossFirst Q hQ j r Λ θ E W).equiv
        (singStepFirst_smul ihW _ n)).trans
      ((singStepCrossFirst Q hQ j r Λ θ E W).map_smul _ _)).trans
      (congrArg (· • (singStepCrossFirst Q hQ j r Λ θ E W).equiv (singStepFirst ihW n))
        (singStepLast_apply Q j r Λ θ E x)))
    (singStepXMap Q hQ j r Λ θ E g) (singStepLastMap Q hQ j r Λ θ E g) hS z
  exact hT

/-- The standardization of all `n + 1` red strands on maps, unfolded one step. -/
theorem singStd_succ_map_hom (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (E : AlgCat.{u} k) {X Y : ModuleCat.{u} (singAlg Q (n + 1) Λ θ ⊗[k] E)} (h : X ⟶ Y)
    (y : (singStd Q hQ (n + 1) Λ θ E).obj X) :
    ((singStd Q hQ (n + 1) Λ θ E).map h).hom y =
      ((ModuleCat.restrictScalars.{u} (singAssocIn Q n Λ θ E) ⋙
      singStd Q hQ n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) (AlgCat.of k (singLast Q Λ θ ⊗[k] E)) ⋙
      ModuleCat.restrictScalars.{u} (singAssocOut Q n Λ θ E) ⋙
      cutSpectFunctor (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
        (θ (Fin.last n)) E hQ).map h).hom y := rfl

theorem singStepCross_equiv
    (x : (singStd Q hQ (j + (r + 1)) Λ θ E).obj
      ((ModuleCat.restrictScalars.{u} (singSplit Q j (r + 1) Λ θ E).toRingHom).obj Z)) :
    (singStepCross Q hQ j r Λ θ E Z).equiv x = x := rfl

theorem singStepCross_map_hom (g : Z ⟶ W)
    (x : (singStd Q hQ (j + (r + 1)) Λ θ E).obj
      ((ModuleCat.restrictScalars.{u} (singSplit Q j (r + 1) Λ θ E).toRingHom).obj Z)) :
    ((ModuleCat.restrictScalars.{u} (singAssocIn Q (j + r) Λ θ E) ⋙
      singStd Q hQ (j + r) Λc θc (AlgCat.of k (singLast Q Λ θ ⊗[k] E)) ⋙
      ModuleCat.restrictScalars.{u} (singAssocOut Q (j + r) Λ θ E) ⋙
      cutSpectFunctor (a := j + r) (r := 1) Q Λ (singWeight (j + r) θc) γs E hQ).map
        ((ModuleCat.restrictScalars.{u} (singSplit Q j (r + 1) Λ θ E).toRingHom).map g)).hom x =
      ((cutSpectFunctor (a := j + r) (r := 1) Q Λ (singWeight (j + r) θc) γs E hQ).map
          (singStepXMap Q hQ j r Λ θ E g)).hom x := rfl

theorem singStepCross_natural (g : Z ⟶ W)
    (x : (singStd Q hQ (j + (r + 1)) Λ θ E).obj
      ((ModuleCat.restrictScalars.{u} (singSplit Q j (r + 1) Λ θ E).toRingHom).obj Z)) :
    (singStepCross Q hQ j r Λ θ E W).equiv
        (((ModuleCat.restrictScalars.{u} (singSplit Q j (r + 1) Λ θ E).toRingHom ⋙
          singStd Q hQ (j + (r + 1)) Λ θ E).map g).hom x) =
      ((cutSpectFunctor (a := j + r) (r := 1) Q Λ (singWeight (j + r) θc) γs E hQ).map
          (singStepXMap Q hQ j r Λ θ E g)).hom ((singStepCross Q hQ j r Λ θ E Z).equiv x) := by
  have e1 := singStepCross_equiv Q hQ j r Λ θ E (Z := W)
    (((ModuleCat.restrictScalars.{u} (singSplit Q j (r + 1) Λ θ E).toRingHom ⋙
      singStd Q hQ (j + (r + 1)) Λ θ E).map g).hom x)
  have e2 := singStd_succ_map_hom Q hQ (j + r) Λ θ E
    ((ModuleCat.restrictScalars.{u} (singSplit Q j (r + 1) Λ θ E).toRingHom).map g) x
  have e2' : ((ModuleCat.restrictScalars.{u} (singSplit Q j (r + 1) Λ θ E).toRingHom ⋙
      singStd Q hQ (j + (r + 1)) Λ θ E).map g).hom x =
      ((ModuleCat.restrictScalars.{u} (singAssocIn Q (j + r) Λ θ E) ⋙
        singStd Q hQ (j + r) Λc θc (AlgCat.of k (singLast Q Λ θ ⊗[k] E)) ⋙
        ModuleCat.restrictScalars.{u} (singAssocOut Q (j + r) Λ θ E) ⋙
        cutSpectFunctor (a := j + r) (r := 1) Q Λ (singWeight (j + r) θc) γs E hQ).map
          ((ModuleCat.restrictScalars.{u} (singSplit Q j (r + 1) Λ θ E).toRingHom).map g)).hom
            x := by
    convert e2 using 2 <;> rfl
  have e3 := singStepCross_map_hom Q hQ j r Λ θ E g x
  have e4 := congrArg (fun y => ((cutSpectFunctor (a := j + r) (r := 1) Q Λ
    (singWeight (j + r) θc) γs E hQ).map (singStepXMap Q hQ j r Λ θ E g)).hom y)
      (singStepCross_equiv Q hQ j r Λ θ E x).symm
  exact e1.trans (e2'.trans (e3.trans e4))

theorem singStepAssoc_equiv
    (z : spectAssocLeft Q Λ θ0 βs γs E hQ (singStepN Q hQ j r Λ θ E W)) :
    (singStepAssoc Q hQ j r Λ θ E W).equiv z =
      spectAssocAddEquiv Q Λ θ0 βs γs E hQ (singStepN Q hQ j r Λ θ E W) z := rfl

theorem singStepAssoc_equiv' (z : spectAssocLeft Q Λ θ0 βs γs E hQ (singStepN Q hQ j r Λ θ E Z)) :
    spectAssocAddEquiv Q Λ θ0 βs γs E hQ (singStepN Q hQ j r Λ θ E Z) z =
      (singStepAssoc Q hQ j r Λ θ E Z).equiv z := rfl

/-- The one-step associativity of the inductive step is natural. -/
theorem singStepAssoc_natural (g : Z ⟶ W)
    (z : spectAssocLeft Q Λ θ0 βs γs E hQ (singStepN Q hQ j r Λ θ E Z)) :
    (singStepAssoc Q hQ j r Λ θ E W).equiv
        (((cutSpectFunctor (a := j + r) (r := 1) Q (Λ ∘ Fin.cast (Nat.add_assoc j r 1))
          (θ0 + βs) γs E hQ).map (singStepLastMap Q hQ j r Λ θ E g)).hom z) =
      ((cutSpectFunctor (a := j) (r := r + 1) Q Λ θ0 (βs + γs) E hQ).map
          (singTailChainIn Q hQ j r Λ θ E g)).hom ((singStepAssoc Q hQ j r Λ θ E Z).equiv z) := by
  have e1 := singStepAssoc_equiv Q hQ j r Λ θ E (W := W)
    (((cutSpectFunctor (a := j + r) (r := 1) Q (Λ ∘ Fin.cast (Nat.add_assoc j r 1))
      (θ0 + βs) γs E hQ).map (singStepLastMap Q hQ j r Λ θ E g)).hom z)
  have h3 := spectAssocAddEquiv_natural (a := j) (m := r) Q Λ θ0 βs γs E hQ
    (N := singStepN Q hQ j r Λ θ E Z) (N' := singStepN Q hQ j r Λ θ E W)
    (singStepNMap Q hQ j r Λ θ E g) z
  have e2 := congrArg (fun y => ((cutSpectFunctor (a := j) (r := r + 1) Q Λ θ0 (βs + γs) E
    hQ).map (singTailChainIn Q hQ j r Λ θ E g)).hom y) (singStepAssoc_equiv' Q hQ j r Λ θ E z)
  have h3' : spectAssocAddEquiv Q Λ θ0 βs γs E hQ (singStepN Q hQ j r Λ θ E W)
      (((cutSpectFunctor (a := j + r) (r := 1) Q (Λ ∘ Fin.cast (Nat.add_assoc j r 1))
        (θ0 + βs) γs E hQ).map (singStepLastMap Q hQ j r Λ θ E g)).hom z) =
      ((cutSpectFunctor (a := j) (r := r + 1) Q Λ θ0 (βs + γs) E hQ).map
          (singTailChainIn Q hQ j r Λ θ E g)).hom
        (spectAssocAddEquiv Q Λ θ0 βs γs E hQ (singStepN Q hQ j r Λ θ E Z) z) := by
    convert h3 using 2
  exact e1.trans (h3'.trans e2)

end Step

/-- **The standardization split at a cut is natural** (Webster, arXiv:1309.3796v3, §5.1):
`singCutEquiv` commutes with the maps induced by a map of modules. -/
theorem singCutEquiv_natural (j : ℕ) : (r : ℕ) → (Λ : Fin (j + r) → I →₀ ℕ) →
    (θ : Fin (j + r) → Multiset I) → (E : AlgCat.{u} k) →
    {Z W : ModuleCat.{u} (singAlg Q j (Λ ∘ Fin.castAdd r) (θ ∘ Fin.castAdd r) ⊗[k]
      (AlgCat.of k (singAlg Q r (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) :
        AlgCat.{u} k))} → (g : Z ⟶ W) →
    ∀ x, (singCutEquiv Q hQ j r Λ θ E W).equiv
        (((ModuleCat.restrictScalars.{u} (singSplit Q j r Λ θ E).toRingHom ⋙
          singStd Q hQ (j + r) Λ θ E).map g).hom x) =
      ((singOuter Q hQ j r Λ θ E ⋙ cutSpectFunctor (a := j) (r := r) Q Λ _ _ E hQ).map g).hom
        ((singCutEquiv Q hQ j r Λ θ E Z).equiv x)
  | 0, Λ, θ, E, _, _, g => fun x => singCutEquivZero_natural Q hQ j Λ θ E g x
  | r + 1, Λ, θ, E, _, _, g => by
    have ih := singCutEquiv_natural j r (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
      (cutLastSpect Q (j + r) Λ (θ (Fin.last (j + r))) E) (singStepZMap Q j r Λ θ E g)
    exact IntertwiningEquiv.ofEq_natural (IntertwiningEquiv.trans_natural
      (IntertwiningEquiv.trans_natural (IntertwiningEquiv.trans_natural
        (singStepCross_natural Q hQ j r Λ θ E g) (singStepSecond_natural g _ _ ih))
        (singStepAssoc_natural Q hQ j r Λ θ E g)) (singStepTail_natural Q hQ j r Λ θ E g))

end Categorification.Stendhal
