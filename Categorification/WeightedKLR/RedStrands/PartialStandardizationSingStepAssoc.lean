/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSingStepFirst

/-!
# The standardization in stages, split at a cut: the inductive step up to associativity

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3 (proof of
Lemma 7.19). In the inductive step from `r` to `r + 1` red strands in the second block, the
standardization of all `j + r + 1` red strands is identified, through the induction hypothesis,
with the left side of the one-step associativity `spectAssocLeft` (`singStepSecond`), and then
with its right side (`singStepAssoc`). The identifications across equal labels, equal weights
and a change of spectator go through `cutSpectTransport`.

## Main definitions

* `Stendhal.tensorProductAlgebraRecast`: the identification along equal labels and weights.
* `Stendhal.cutSpectTransport`: partial standardization at a cut, transported along equal labels
  and weights and a change of spectator.
* `Stendhal.singStepSecond`, `Stendhal.singStepAssoc`: the inductive step up to the one-step
  associativity, and the one-step associativity.

## Main results

* `Stendhal.tensorTriple_addHom_ext`: additive maps on a triple tensor product agreeing on pure
  tensors agree.
* `Stendhal.singStepLast_apply`: the compatibility of the algebra maps at the last cut.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra TypeA
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I k : Type u} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q)

/-- The identification of tensor product algebras of equal labels and equal weights. -/
def tensorProductAlgebraRecast {n : ℕ} {Λ Λ' : Fin n → I →₀ ℕ} (hΛ : Λ = Λ') {ν ν' : Multiset I}
    (hν : ν = ν') : TensorProductAlgebra k Q Λ ν ≃ₐ[k] TensorProductAlgebra k Q Λ' ν' := by
  subst hΛ hν; exact AlgEquiv.refl

/-- Two additive maps on a triple tensor product agreeing on pure tensors agree. -/
theorem tensorTriple_addHom_ext {M N P R : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] [AddCommGroup P] [Module k P] [AddCommGroup R]
    (F G : (M ⊗[k] N) ⊗[k] P →+ R) (h : ∀ m n p, F ((m ⊗ₜ n) ⊗ₜ p) = G ((m ⊗ₜ n) ⊗ₜ p))
    (x : (M ⊗[k] N) ⊗[k] P) : F x = G x := by
  induction x using TensorProduct.inductionOn with
  | tmul d p =>
    induction d using TensorProduct.inductionOn with
    | tmul m n => exact h m n p
    | add d d' hd hd' => rw [TensorProduct.add_tmul, map_add, map_add, hd, hd']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

section Transport

variable {a r : ℕ} {Λ Λ' : Fin (a + r) → I →₀ ℕ} (hΛ : Λ = Λ') {θ θ' β β' : Multiset I}
  (hθ : θ = θ') (hβ : β = β') {E E' : AlgCat.{u} k} (φ : E →ₐ[k] E')

/-- The identification of the algebras of a cut along equal labels and weights and a map of
spectators. -/
def cutSpectRecast : cutSpectAlgebra Q Λ θ β E →ₐ[k] cutSpectAlgebra Q Λ' θ' β' E' :=
  Algebra.TensorProduct.map (Algebra.TensorProduct.map
    (tensorProductAlgebraRecast Q (congrArg (· ∘ Fin.castAdd r) hΛ) hθ).toAlgHom
    (tensorProductAlgebraRecast Q (congrArg (· ∘ Fin.natAdd a) hΛ) hβ).toAlgHom) φ

/-- The identification of the algebras of all strands of a cut along equal labels and weights
and a map of spectators. -/
def cutSpectTotalRecast :
    TensorProductAlgebra k Q Λ (θ + β) ⊗[k] E →ₐ[k] TensorProductAlgebra k Q Λ' (θ' + β') ⊗[k] E' :=
  Algebra.TensorProduct.map
    (tensorProductAlgebraRecast Q hΛ (congrArg₂ (· + ·) hθ hβ)).toAlgHom φ

variable {N : ModuleCat.{u} (cutSpectAlgebra Q Λ θ β E)}
  {N' : ModuleCat.{u} (cutSpectAlgebra Q Λ' θ' β' E')}

/-- **Partial standardization at a cut, transported along equal labels and weights** and a
change of spectator. -/
def cutSpectTransport (f : N ≃+ N')
    (hf : ∀ (x : cutSpectAlgebra Q Λ θ β E) (n : N),
      f (x • n) = cutSpectRecast Q hΛ hθ hβ φ x • f n) :
    IntertwiningEquiv (cutSpectTotalRecast Q hΛ hθ hβ φ).toRingHom
      ((cutSpectFunctor Q Λ θ β E hQ).obj N) ((cutSpectFunctor Q Λ' θ' β' E' hQ).obj N') := by
  subst hΛ hθ hβ
  exact
    { equiv := cutSpectStandardEquivOf Q Λ θ β φ (N := N) (N' := N') f
        (fun x n => (hf x n).trans (congrArg (· • f n)
          (congrArg (fun F => Algebra.TensorProduct.map F φ x)
            (Algebra.TensorProduct.map_id (R := k) (S := k)
              (A := TensorProductAlgebra k Q (Λ ∘ Fin.castAdd r) θ)
              (B := TensorProductAlgebra k Q (Λ ∘ Fin.natAdd a) β))))) hQ
      map_smul := fun x z => (cutSpectStandardEquivOf_smul Q Λ θ β φ _ _ hQ x z) }

end Transport

section Step

variable (j r : ℕ) (Λ : Fin (j + (r + 1)) → I →₀ ℕ) (θ : Fin (j + (r + 1)) → Multiset I)
  (E : AlgCat.{u} k)
  (Z : ModuleCat.{u} (singAlg Q j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1)) ⊗[k]
    (AlgCat.of k (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) :
      AlgCat.{u} k)))

local notation "Λc" => Λ ∘ Fin.castSucc
local notation "θc" => θ ∘ Fin.castSucc
local notation "Es" => cutLastSpect Q (j + r) Λ (θ (Fin.last (j + r))) E
local notation "θ0" => singWeight j (θc ∘ Fin.castAdd r)
local notation "βs" => singWeight r (θc ∘ Fin.natAdd j)
local notation "γs" => θ (Fin.last (j + r))

set_option hygiene false in
local notation "ΛA" => blocksLeftLabels (a := j) (m := r) (r := 1)
  (Λ ∘ Fin.cast (Nat.add_assoc j r 1))
set_option hygiene false in
local notation "EL" => (AlgCat.of k (blocksLastAlgebra (a := j) (m := r) (r := 1) Q
  (Λ ∘ Fin.cast (Nat.add_assoc j r 1)) γs ⊗[k] E) : AlgCat.{u} k)

/-- The spectator of the step, in the form of the one-step associativity. -/
def singStepSpectId : Es →ₐ[k] EL := AlgHom.id k _

/-- The identification of the algebras at the first cut is the identity. -/
theorem singStepRecast_apply (x : cutSpectAlgebra (a := j) (r := r) Q Λc θ0 βs Es) :
    cutSpectRecast Q (Λ := Λc) (Λ' := ΛA) rfl (rfl : θ0 = θ0) (rfl : βs = βs)
      (singStepSpectId Q j r Λ θ E) x = x :=
  (congrArg (fun F => Algebra.TensorProduct.map F (singStepSpectId Q j r Λ θ E) x)
    (Algebra.TensorProduct.map_id (R := k) (S := k)
      (A := TensorProductAlgebra k Q (Λc ∘ Fin.castAdd r) θ0)
      (B := TensorProductAlgebra k Q (Λc ∘ Fin.natAdd j) βs))).trans
    (tensorMap_id_id_apply (k := k) x)

/-- `singStepLeftAlg` is `spectAssocLeftAlg` after the identification. -/
theorem singStepLeftAlg_recast (x : cutSpectAlgebra (a := j) (r := r) Q Λc θ0 βs Es) :
    singStepLeftAlg Q j r Λ θ E x = spectAssocLeftAlg Q Λ θ0 βs γs E
      (cutSpectRecast Q (Λ := Λc) (Λ' := ΛA) rfl (rfl : θ0 = θ0) (rfl : βs = βs)
        (singStepSpectId Q j r Λ θ E) x) :=
  congrArg (spectAssocLeftAlg Q Λ θ0 βs γs E) (singStepRecast_apply Q j r Λ θ E x).symm

/-- The action on `singStepLeftIn` is the action on `spectLeftInput`. -/
theorem singStepCrossFirst_smul (x : cutSpectAlgebra (a := j) (r := r) Q Λc θ0 βs Es)
    (n : singStepLeftIn Q hQ j r Λ θ E Z) :
    (x • n : singStepLeftIn Q hQ j r Λ θ E Z) =
      (cutSpectRecast Q (Λ := Λc) (Λ' := ΛA) rfl (rfl : θ0 = θ0) (rfl : βs = βs)
        (singStepSpectId Q j r Λ θ E) x •
        (show spectLeftInput Q Λ θ0 βs γs E (singStepN Q hQ j r Λ θ E Z) from n) :
        spectLeftInput Q Λ θ0 βs γs E (singStepN Q hQ j r Λ θ E Z)) :=
  congrArg (· • (show singStepN Q hQ j r Λ θ E Z from n)) (singStepLeftAlg_recast Q j r Λ θ E x)

/-- The partial standardization at the first cut of the step, in the form of the one-step
associativity. -/
def singStepCrossFirst := cutSpectTransport Q hQ (Λ := Λc) (Λ' := ΛA) rfl (rfl : θ0 = θ0)
    (rfl : βs = βs) (singStepSpectId Q j r Λ θ E) (N := singStepLeftIn Q hQ j r Λ θ E Z)
    (N' := spectLeftInput Q Λ θ0 βs γs E (singStepN Q hQ j r Λ θ E Z)) (AddEquiv.refl _)
    (singStepCrossFirst_smul Q hQ j r Λ θ E Z)

/-- The algebra maps at the last cut agree. -/
theorem singStepLast_apply (x : cutSpectAlgebra (a := j + r) (r := 1) Q Λ
      (singWeight (j + r) θc) γs E) :
    cutSpectTotalRecast Q (Λ := Λc) (Λ' := ΛA) rfl (rfl : θ0 = θ0) (rfl : βs = βs)
        (singStepSpectId Q j r Λ θ E)
        (singWeightCast Q j r Λc θc Es (cutLastAssoc Q (j + r) Λ (singWeight (j + r) θc) γs E x)) =
      spectLastAlg Q Λ θ0 βs γs E
        (cutSpectRecast Q (a := j + r) (r := 1) (Λ := Λ) (Λ' := Λ ∘ Fin.cast (Nat.add_assoc j r 1))
          rfl (singWeight_add j r θc) (rfl : γs = γs) (AlgHom.id k E) x) := by
  exact tensorTriple_addHom_ext (k := k)
    ((cutSpectTotalRecast Q (Λ := Λc) (Λ' := ΛA) rfl (rfl : θ0 = θ0) (rfl : βs = βs)
        (singStepSpectId Q j r Λ θ E)).toRingHom.toAddMonoidHom.comp
      ((singWeightCast Q j r Λc θc Es).toRingHom.toAddMonoidHom.comp
        (cutLastAssoc Q (j + r) Λ (singWeight (j + r) θc) γs E).toAddMonoidHom))
    ((spectLastAlg Q Λ θ0 βs γs E).toRingHom.toAddMonoidHom.comp
      (cutSpectRecast Q (a := j + r) (r := 1) (Λ := Λ) (Λ' := Λ ∘ Fin.cast (Nat.add_assoc j r 1))
          rfl (singWeight_add j r θc) (rfl : γs = γs) (AlgHom.id k E)).toRingHom.toAddMonoidHom)
    (fun _ _ _ => rfl) x

variable {Q hQ j r Λ θ E Z} in
/-- **The left side of the inductive step**: from the induction hypothesis, the standardization
of all `j + r + 1` red strands is the left side of the one-step associativity. -/
def singStepSecond
    (ih : IntertwiningEquiv (singWeightCast Q j r Λc θc Es).toRingHom
      ((singStd Q hQ (j + r) Λc θc Es).obj
        ((ModuleCat.restrictScalars.{u} (singSplit Q j r Λc θc Es).toRingHom).obj
          (singStepZ Q j r Λ θ E Z)))
      ((cutSpectFunctor (a := j) (r := r) Q Λc θ0 βs Es hQ).obj
        (singStepOuter Q hQ j r Λ θ E Z))) :
    IntertwiningEquiv (cutSpectTotalRecast Q (a := j + r) (r := 1) (Λ := Λ)
        (Λ' := Λ ∘ Fin.cast (Nat.add_assoc j r 1)) rfl (singWeight_add j r θc) (rfl : γs = γs)
        (AlgHom.id k E)).toRingHom
      ((cutSpectFunctor (a := j + r) (r := 1) Q Λ (singWeight (j + r) θc) γs E hQ).obj
        (cutLastObj Q (j + r) Λ (singWeight (j + r) θc) γs E (singStepX Q hQ j r Λ θ E Z)))
      (spectAssocLeft Q Λ θ0 βs γs E hQ (singStepN Q hQ j r Λ θ E Z)) :=
  cutSpectTransport Q hQ (a := j + r) (r := 1) (Λ := Λ)
    (Λ' := Λ ∘ Fin.cast (Nat.add_assoc j r 1)) rfl (singWeight_add j r θc) (rfl : γs = γs)
    (AlgHom.id k E)
    (N := cutLastObj Q (j + r) Λ (singWeight (j + r) θc) γs E (singStepX Q hQ j r Λ θ E Z))
    (N' := (ModuleCat.restrictScalars.{u} (spectLastAlg Q Λ θ0 βs γs E).toRingHom).obj
      ((cutSpectFunctor (a := j) (r := r) Q ΛA θ0 βs EL hQ).obj
        (spectLeftInput Q Λ θ0 βs γs E (singStepN Q hQ j r Λ θ E Z))))
    ((singStepFirst ih).trans (singStepCrossFirst Q hQ j r Λ θ E Z).equiv)
    (fun x n => ((congrArg (singStepCrossFirst Q hQ j r Λ θ E Z).equiv
        (singStepFirst_smul ih _ n)).trans
      ((singStepCrossFirst Q hQ j r Λ θ E Z).map_smul _ _)).trans
      (congrArg (· • (singStepCrossFirst Q hQ j r Λ θ E Z).equiv (singStepFirst ih n))
        (singStepLast_apply Q j r Λ θ E x)))

/-- The one-step associativity of the step, as an intertwining isomorphism. -/
def singStepAssoc : IntertwiningEquiv (spectWeightAssoc Q Λ θ0 βs γs E).toRingHom
    (spectAssocLeft Q Λ θ0 βs γs E hQ (singStepN Q hQ j r Λ θ E Z))
    (spectAssocRight Q Λ θ0 βs γs E hQ (singStepN Q hQ j r Λ θ E Z)) where
  equiv := (spectAssocLinearEquiv Q Λ θ0 βs γs E hQ (singStepN Q hQ j r Λ θ E Z)).toAddEquiv
  map_smul := spectAssocAddEquiv_smul Q Λ θ0 βs γs E hQ (singStepN Q hQ j r Λ θ E Z)

end Step

end Categorification.Stendhal
