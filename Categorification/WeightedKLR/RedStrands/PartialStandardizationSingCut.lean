/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSingStepAssoc

/-!
# The standardization with singleton blocks, split at a cut

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3 (proof of
Lemma 7.19, where the standardization with singleton blocks is computed in stages). The
standardization in stages of `j + r` red strands with singleton blocks is the partial
standardization at the cut after the `j`-th red strand of the standardizations in stages of the
two blocks (`singCutEquiv`). The proof is by induction on `r`. The inductive step identifies
the right side of the one-step associativity with the partial standardization at the cut of the
standardizations of the two blocks (`singStepTail`), through changes of spectator of the two
blocks.

## Main definitions

* `Stendhal.IntertwiningEquiv.ofObjEq`: an equality of modules as an intertwining isomorphism.
* `Stendhal.singStepTail`: the right side of the inductive step.
* `Stendhal.singCutEquiv`: the standardization with singleton blocks, split at a cut.

## Main results

* `Stendhal.tensorProductAlgebraCast_cancel`: two casts along equal labels cancel.
* `Stendhal.tensorQuadRight_addHom_ext`, `Stendhal.tensorQuadMid_addHom_ext`: additive maps on
  fourfold tensor products agreeing on pure tensors agree.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra TypeA
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I k : Type u} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q)

/-- Two casts along equal labels cancel. -/
theorem tensorProductAlgebraCast_cancel {m : ℕ} {Λ₁ Λ₂ : Fin m → I →₀ ℕ} (h h' : Λ₁ = Λ₂)
    (ν : Multiset I) (t : TensorProductAlgebra k Q Λ₂ ν) :
    tensorProductAlgebraCast Q h ν ((tensorProductAlgebraCast Q h' ν).symm t) = t :=
  (tensorProductAlgebraCast Q h ν).apply_symm_apply t

/-- Additive maps on `M ⊗ (N ⊗ (P ⊗ R))` agreeing on pure tensors agree. -/
theorem tensorQuadRight_addHom_ext {M N P R S : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] [AddCommGroup P] [Module k P] [AddCommGroup R] [Module k R]
    [AddCommGroup S] (F G : M ⊗[k] (N ⊗[k] (P ⊗[k] R)) →+ S)
    (h : ∀ m n p q, F (m ⊗ₜ (n ⊗ₜ (p ⊗ₜ q))) = G (m ⊗ₜ (n ⊗ₜ (p ⊗ₜ q))))
    (x : M ⊗[k] (N ⊗[k] (P ⊗[k] R))) : F x = G x := by
  induction x using TensorProduct.inductionOn with
  | tmul m y =>
    induction y using TensorProduct.inductionOn with
    | tmul n z =>
      induction z using TensorProduct.inductionOn with
      | tmul p q => exact h m n p q
      | add z z' hz hz' => rw [TensorProduct.tmul_add, TensorProduct.tmul_add, map_add,
          map_add, hz, hz']
    | add y y' hy hy' => rw [TensorProduct.tmul_add, map_add, map_add, hy, hy']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Additive maps on `(M ⊗ N) ⊗ (P ⊗ R)` agreeing on pure tensors agree. -/
theorem tensorQuadMid_addHom_ext {M N P R S : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] [AddCommGroup P] [Module k P] [AddCommGroup R] [Module k R]
    [AddCommGroup S] (F G : (M ⊗[k] N) ⊗[k] (P ⊗[k] R) →+ S)
    (h : ∀ m n p q, F ((m ⊗ₜ n) ⊗ₜ (p ⊗ₜ q)) = G ((m ⊗ₜ n) ⊗ₜ (p ⊗ₜ q)))
    (x : (M ⊗[k] N) ⊗[k] (P ⊗[k] R)) : F x = G x := by
  induction x using TensorProduct.inductionOn with
  | tmul y z =>
    induction y using TensorProduct.inductionOn with
    | tmul m n =>
      induction z using TensorProduct.inductionOn with
      | tmul p q => exact h m n p q
      | add z z' hz hz' => rw [TensorProduct.tmul_add, map_add, map_add, hz, hz']
    | add y y' hy hy' => rw [TensorProduct.add_tmul, map_add, map_add, hy, hy']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- An equality of modules, as an intertwining isomorphism along the identity. -/
def IntertwiningEquiv.ofObjEq {R : Type u} [Ring R] {X Y : ModuleCat.{u} R} (h : X = Y) :
    IntertwiningEquiv (RingHom.id R) X Y := by
  subst h
  exact ⟨AddEquiv.refl _, fun _ _ => rfl⟩

section Tail

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
local notation "Hd" => TensorProductAlgebra k Q (Λ ∘ Fin.castAdd (r + 1))
  (singWeight j (θ ∘ Fin.castAdd (r + 1)))
set_option hygiene false in
local notation "Hd'" => TensorProductAlgebra k Q (Λc ∘ Fin.castAdd r) θ0
set_option hygiene false in
local notation "Lt" => singLast Q (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)

/-- `singHeadMap` as a map of spectators. -/
def singTailHeadMap :
    (AlgCat.of k (singAlg Q r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j) ⊗[k] Es) : AlgCat.{u} k)
      →ₐ[k] (AlgCat.of k (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) :
        AlgCat.{u} k) :=
  singHeadMap Q j r Λ θ E

/-- The change of spectator of the first block in the tail of the step. -/
def singTailHead : SpectatorEquiv Hd (singTailHeadMap Q j r Λ θ E)
    ((singStd Q hQ j (Λc ∘ Fin.castAdd r) (θc ∘ Fin.castAdd r)
      (AlgCat.of k (singAlg Q r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j) ⊗[k] Es))).obj
        (singStepZ Q j r Λ θ E Z))
    ((singStd Q hQ j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1))
      (AlgCat.of k (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E))).obj Z) :=
  singStdSpectatorEquiv Q hQ j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1))
    (singTailHeadMap Q j r Λ θ E) (Z := singStepZ Q j r Λ θ E Z) (Z' := Z)
    ⟨AddEquiv.refl _, fun _ _ => rfl⟩

/-- The spectator `T^A ⊗ E` of the second block in the tail of the step. -/
def singTailHE : AlgCat.{u} k := AlgCat.of k (Hd ⊗[k] E)

/-- The spectator `T^R ⊗ (T^A ⊗ E)` of the first `r` singleton blocks of the second block. -/
def singTailTgt : AlgCat.{u} k := AlgCat.of k (Lt ⊗[k] singTailHE Q j r Λ θ E)

/-- The spectator map `T^A ⊗ (T^R ⊗ E) → T^R ⊗ (T^A ⊗ E)` of the tail of the step. -/
def singTailPsi : (AlgCat.of k (Hd' ⊗[k] Es) : AlgCat.{u} k) →ₐ[k] singTailTgt Q j r Λ θ E :=
  (Algebra.TensorProduct.leftComm k Hd Lt E).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id k Hd)
      (Algebra.TensorProduct.map
        (tensorProductAlgebraCast Q (natAdd_natAdd_labels j r Λ) (θ (Fin.last (j + r)))).toAlgHom
        (AlgHom.id k E)))

/-- The rotation `A ⊗ (T^A ⊗ E) → T^A ⊗ (A ⊗ E)` of `singOuter` at `r + 1`. -/
def singTailLeftComm : singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k]
      singTailHE Q j r Λ θ E →+*
    Hd ⊗[k] (AlgCat.of k (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) :
      AlgCat.{u} k) :=
  (Algebra.TensorProduct.leftComm k
    (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)) Hd E).toAlgHom.toRingHom

/-- The first stage of `singOuter` in the step, as a module over the second block. -/
abbrev singTailV : ModuleCat.{u} (singAlg Q r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j) ⊗[k]
    (AlgCat.of k (TensorProductAlgebra k Q (Λc ∘ Fin.castAdd r) θ0 ⊗[k] Es) : AlgCat.{u} k)) :=
  (ModuleCat.restrictScalars.{u} (Algebra.TensorProduct.leftComm k
      (singAlg Q r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j))
      (TensorProductAlgebra k Q (Λc ∘ Fin.castAdd r) θ0) Es).toAlgHom.toRingHom).obj
    ((singStd Q hQ j (Λc ∘ Fin.castAdd r) (θc ∘ Fin.castAdd r)
      (AlgCat.of k (singAlg Q r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j) ⊗[k] Es))).obj
        (singStepZ Q j r Λ θ E Z))

/-- The first stage of `singOuter` at `r + 1`, as a module over the second block. -/
abbrev singTailW₀ : ModuleCat.{u} (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k]
    singTailHE Q j r Λ θ E) :=
  (ModuleCat.restrictScalars.{u} (singTailLeftComm Q j r Λ θ E)).obj
    ((singStd Q hQ j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1))
      (AlgCat.of k (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E))).obj Z)

/-- The first stage of `singOuter` at `r + 1`, as a module over the first `r` singleton blocks
of the second block. -/
abbrev singTailW : ModuleCat.{u} (singAlg Q r ((Λ ∘ Fin.natAdd j) ∘ Fin.castSucc)
    ((θ ∘ Fin.natAdd j) ∘ Fin.castSucc) ⊗[k] singTailTgt Q j r Λ θ E) :=
  (ModuleCat.restrictScalars.{u} (singAssocIn Q r (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)
      (singTailHE Q j r Λ θ E))).obj (singTailW₀ Q hQ j r Λ θ E Z)

/-- The algebra maps of the change of spectator of the second block agree. -/
theorem singTailMid_apply (x : singAlg Q r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j) ⊗[k]
    (AlgCat.of k (Hd' ⊗[k] Es) : AlgCat.{u} k)) :
    Algebra.TensorProduct.map (AlgHom.id k Hd) (singTailHeadMap Q j r Λ θ E)
        (Algebra.TensorProduct.leftComm k
          (singAlg Q r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j)) Hd' Es x) =
      singTailLeftComm Q j r Λ θ E
        (singAssocIn Q r (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) (singTailHE Q j r Λ θ E)
          (Algebra.TensorProduct.map (AlgHom.id k _) (singTailPsi Q j r Λ θ E) x)) :=
  tensorQuadRight_addHom_ext (k := k)
    ((Algebra.TensorProduct.map (AlgHom.id k Hd)
        (singTailHeadMap Q j r Λ θ E)).toRingHom.toAddMonoidHom.comp
      (Algebra.TensorProduct.leftComm k
        (singAlg Q r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j)) Hd' Es).toRingHom.toAddMonoidHom)
    ((singTailLeftComm Q j r Λ θ E).toAddMonoidHom.comp
      ((singAssocIn Q r (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)
          (singTailHE Q j r Λ θ E)).toAddMonoidHom.comp
        (Algebra.TensorProduct.map (AlgHom.id k _)
          (singTailPsi Q j r Λ θ E)).toRingHom.toAddMonoidHom))
    (fun _ _ _ _ => rfl) x

/-- The change of spectator of the second block in the tail of the step. -/
def singTailMid : SpectatorEquiv (singAlg Q r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j))
    (singTailPsi Q j r Λ θ E) (singTailV Q hQ j r Λ θ E Z) (singTailW Q hQ j r Λ θ E Z) where
  equiv := (singTailHead Q hQ j r Λ θ E Z).equiv
  map_smul x m := ((singTailHead Q hQ j r Λ θ E Z).map_smul (Algebra.TensorProduct.leftComm k
      (singAlg Q r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j)) Hd' Es x) m).trans
    (congrArg (· • (singTailHead Q hQ j r Λ θ E Z).equiv m) (singTailMid_apply Q j r Λ θ E x))

/-- The standardization of the second block, changing the spectator. -/
def singTailSecond := singStdSpectatorEquiv Q hQ r (Λc ∘ Fin.natAdd j) (θc ∘ Fin.natAdd j)
  (singTailPsi Q j r Λ θ E) (Z := singTailV Q hQ j r Λ θ E Z) (Z' := singTailW Q hQ j r Λ θ E Z)
  (singTailMid Q hQ j r Λ θ E Z)

set_option hygiene false in
local notation "H0" => TensorProductAlgebra k Q (Λ ∘ Fin.castAdd (r + 1)) θ0

/-- The identification of the spectator `T^A ⊗ E` of the tail. -/
def singTailSpectId : (AlgCat.of k (H0 ⊗[k] E) : AlgCat.{u} k) →ₐ[k] singTailHE Q j r Λ θ E :=
  AlgHom.id k _

/-- The input of the last stage of the standardization of the second block at `r + 1`. -/
abbrev singTailInner : ModuleCat.{u} (cutSpectAlgebra (a := r) (r := 1) Q (Λ ∘ Fin.natAdd j)
    (singWeight r ((θ ∘ Fin.natAdd j) ∘ Fin.castSucc)) ((θ ∘ Fin.natAdd j) (Fin.last r))
    (singTailHE Q j r Λ θ E)) :=
  (ModuleCat.restrictScalars.{u} (singAssocOut Q r (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)
      (singTailHE Q j r Λ θ E))).obj
    ((singStd Q hQ r ((Λ ∘ Fin.natAdd j) ∘ Fin.castSucc) ((θ ∘ Fin.natAdd j) ∘ Fin.castSucc)
      (singTailTgt Q j r Λ θ E)).obj (singTailW Q hQ j r Λ θ E Z))

/-- The algebra maps of the inner stage of the tail agree. -/
theorem singTailInner_apply (x : cutSpectAlgebra (a := r) (r := 1) Q (Λ ∘ Fin.natAdd j) βs γs
    (AlgCat.of k (H0 ⊗[k] E) : AlgCat.{u} k)) :
    Algebra.TensorProduct.map (AlgHom.id k _) (singTailPsi Q j r Λ θ E)
        (singRotOut Q j r Λc θ0 βs Es (singStepLeftInv Q j r Λ θ E
          (spectAssocRightAlg Q Λ θ0 βs γs E x))) =
      singAssocOut Q r (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) (singTailHE Q j r Λ θ E)
        (cutSpectRecast Q (a := r) (r := 1) (Λ := Λ ∘ Fin.natAdd j) (Λ' := Λ ∘ Fin.natAdd j)
          rfl (rfl : βs = singWeight r ((θ ∘ Fin.natAdd j) ∘ Fin.castSucc))
          (rfl : γs = (θ ∘ Fin.natAdd j) (Fin.last r)) (singTailSpectId Q j r Λ θ E) x) :=
  tensorQuadMid_addHom_ext (k := k)
    ((Algebra.TensorProduct.map (AlgHom.id k _)
        (singTailPsi Q j r Λ θ E)).toRingHom.toAddMonoidHom.comp
      ((singRotOut Q j r Λc θ0 βs Es).toRingHom.toAddMonoidHom.comp
        ((singStepLeftInv Q j r Λ θ E).toRingHom.toAddMonoidHom.comp
          (spectAssocRightAlg Q Λ θ0 βs γs E).toRingHom.toAddMonoidHom)))
    ((singAssocOut Q r (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)
        (singTailHE Q j r Λ θ E)).toAddMonoidHom.comp
      (cutSpectRecast Q (a := r) (r := 1) (Λ := Λ ∘ Fin.natAdd j) (Λ' := Λ ∘ Fin.natAdd j)
          rfl (rfl : βs = singWeight r ((θ ∘ Fin.natAdd j) ∘ Fin.castSucc))
          (rfl : γs = (θ ∘ Fin.natAdd j) (Fin.last r))
          (singTailSpectId Q j r Λ θ E)).toRingHom.toAddMonoidHom)
    (fun m l h e => congrArg (fun l' => (m ⊗ₜ[k] (l' ⊗ₜ[k] (h ⊗ₜ[k] e)) :
        TensorProductAlgebra k Q ((Λ ∘ Fin.natAdd j) ∘ Fin.castSucc) βs ⊗[k]
          singTailTgt Q j r Λ θ E))
      (tensorProductAlgebraCast_cancel Q (natAdd_natAdd_labels j r Λ)
        (congrArg (Λ ∘ ·) (cast_natAdd (a := j) (m := r) (r := 1))) γs l)) x

/-- The last stage of the standardization of the second block, from the right side of the
one-step associativity. -/
def singTailThird := cutSpectTransport Q hQ (a := r) (r := 1) (Λ := Λ ∘ Fin.natAdd j)
    (Λ' := Λ ∘ Fin.natAdd j) rfl (rfl : βs = singWeight r ((θ ∘ Fin.natAdd j) ∘ Fin.castSucc))
    (rfl : γs = (θ ∘ Fin.natAdd j) (Fin.last r)) (singTailSpectId Q j r Λ θ E)
    (N := spectRightInput Q Λ θ0 βs γs E (singStepN Q hQ j r Λ θ E Z))
    (N' := singTailInner Q hQ j r Λ θ E Z) (singTailSecond Q hQ j r Λ θ E Z).equiv
    (fun x n => ((singTailSecond Q hQ j r Λ θ E Z).map_smul
      (singRotOut Q j r Λc θ0 βs Es (singStepLeftInv Q j r Λ θ E
        (spectAssocRightAlg Q Λ θ0 βs γs E x))) n).trans
      (congrArg (· • (singTailSecond Q hQ j r Λ θ E Z).equiv n)
        (singTailInner_apply Q j r Λ θ E x)))

/-- The identification of the spectator `T^A ⊗ E` of the tail, back. -/
def singTailSpectBack : singTailHE Q j r Λ θ E →ₐ[k] (AlgCat.of k (Hd ⊗[k] E) : AlgCat.{u} k) :=
  AlgHom.id k _

/-- The standardization of the second block at `r + 1`, changing the spectator back. -/
def singTailFourth := singStdSpectatorEquiv Q hQ (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)
  (singTailSpectBack Q j r Λ θ E) (Z := singTailW₀ Q hQ j r Λ θ E Z)
  (Z' := (ModuleCat.restrictScalars.{u} (Algebra.TensorProduct.leftComm k
        (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)) Hd E).toAlgHom.toRingHom).obj
      ((singStd Q hQ j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1))
        (AlgCat.of k (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E))).obj Z))
  ⟨AddEquiv.refl _, fun x m => congrArg (fun y => singTailLeftComm Q j r Λ θ E y •
    (show ((singStd Q hQ j (Λ ∘ Fin.castAdd (r + 1)) (θ ∘ Fin.castAdd (r + 1))
        (AlgCat.of k (singAlg Q (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E))).obj Z)
      from m)) (tensorMap_id_id_apply (k := k) x).symm⟩

/-- The algebra maps of the outer stage of the tail agree. -/
theorem singTailOuter_apply (x : cutSpectAlgebra (a := j) (r := r + 1) Q Λ θ0 (βs + γs) E) :
    Algebra.TensorProduct.map (AlgHom.id k _) (singTailSpectBack Q j r Λ θ E)
        (cutSpectTotalRecast Q (a := r) (r := 1) (Λ := Λ ∘ Fin.natAdd j)
          (Λ' := Λ ∘ Fin.natAdd j) rfl
          (rfl : βs = singWeight r ((θ ∘ Fin.natAdd j) ∘ Fin.castSucc))
          (rfl : γs = (θ ∘ Fin.natAdd j) (Fin.last r)) (singTailSpectId Q j r Λ θ E)
          (spectHeadAlg Q Λ θ0 βs γs E x)) =
      singRotOut Q j (r + 1) Λ (singWeight j (θ ∘ Fin.castAdd (r + 1)))
        (singWeight (r + 1) (θ ∘ Fin.natAdd j)) E
        (cutSpectRecast Q (a := j) (r := r + 1) (Λ := Λ) (Λ' := Λ) rfl
          (rfl : θ0 = singWeight j (θ ∘ Fin.castAdd (r + 1)))
          (rfl : βs + γs = singWeight (r + 1) (θ ∘ Fin.natAdd j)) (AlgHom.id k E) x) :=
  tensorTriple_addHom_ext (k := k)
    ((Algebra.TensorProduct.map (AlgHom.id k _)
        (singTailSpectBack Q j r Λ θ E)).toRingHom.toAddMonoidHom.comp
      ((cutSpectTotalRecast Q (a := r) (r := 1) (Λ := Λ ∘ Fin.natAdd j)
          (Λ' := Λ ∘ Fin.natAdd j) rfl
          (rfl : βs = singWeight r ((θ ∘ Fin.natAdd j) ∘ Fin.castSucc))
          (rfl : γs = (θ ∘ Fin.natAdd j) (Fin.last r))
          (singTailSpectId Q j r Λ θ E)).toRingHom.toAddMonoidHom.comp
        (spectHeadAlg Q Λ θ0 βs γs E).toRingHom.toAddMonoidHom))
    ((singRotOut Q j (r + 1) Λ (singWeight j (θ ∘ Fin.castAdd (r + 1)))
        (singWeight (r + 1) (θ ∘ Fin.natAdd j)) E).toRingHom.toAddMonoidHom.comp
      (cutSpectRecast Q (a := j) (r := r + 1) (Λ := Λ) (Λ' := Λ) rfl
          (rfl : θ0 = singWeight j (θ ∘ Fin.castAdd (r + 1)))
          (rfl : βs + γs = singWeight (r + 1) (θ ∘ Fin.natAdd j))
          (AlgHom.id k E)).toRingHom.toAddMonoidHom)
    (fun _ _ _ => rfl) x

/-- The standardization of the second block at `r + 1`, unfolded at the last red strand. -/
def singTailCross : IntertwiningEquiv (RingHom.id (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd j)
      (singWeight (r + 1) (θ ∘ Fin.natAdd j)) ⊗[k] singTailHE Q j r Λ θ E))
    ((cutSpectFunctor (a := r) (r := 1) Q (Λ ∘ Fin.natAdd j)
      (singWeight r ((θ ∘ Fin.natAdd j) ∘ Fin.castSucc)) ((θ ∘ Fin.natAdd j) (Fin.last r))
      (singTailHE Q j r Λ θ E) hQ).obj (singTailInner Q hQ j r Λ θ E Z))
    ((singStd Q hQ (r + 1) (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) (singTailHE Q j r Λ θ E)).obj
      (singTailW₀ Q hQ j r Λ θ E Z)) :=
  IntertwiningEquiv.ofObjEq rfl

set_option hygiene false in
local notation "NN" => (ModuleCat.restrictScalars.{u} (spectHeadAlg Q Λ θ0 βs γs E).toRingHom).obj
      ((cutSpectFunctor (a := r) (r := 1) Q (Λ ∘ Fin.natAdd j) βs γs
          (AlgCat.of k (H0 ⊗[k] E)) hQ).obj
        (spectRightInput Q Λ θ0 βs γs E (singStepN Q hQ j r Λ θ E Z)))

/-- The tail of the step before the outer stage. -/
def singTailChain := ((singTailThird Q hQ j r Λ θ E Z).trans (singTailCross Q hQ j r Λ θ E Z)).trans
  (IntertwiningEquiv.ofSpectator (singTailFourth Q hQ j r Λ θ E Z))

/-- `singTailChain` intertwines the actions. -/
theorem singTailChain_smul (x : cutSpectAlgebra (a := j) (r := r + 1) Q Λ θ0 (βs + γs) E)
    (n : NN) :
    (singTailChain Q hQ j r Λ θ E Z).equiv (x • n) =
      cutSpectRecast Q (a := j) (r := r + 1) (Λ := Λ) (Λ' := Λ) rfl
          (rfl : θ0 = singWeight j (θ ∘ Fin.castAdd (r + 1)))
          (rfl : βs + γs = singWeight (r + 1) (θ ∘ Fin.natAdd j)) (AlgHom.id k E) x •
        (show (singOuter Q hQ j (r + 1) Λ θ E).obj Z from
          (singTailChain Q hQ j r Λ θ E Z).equiv n) :=
  ((singTailChain Q hQ j r Λ θ E Z).map_smul (spectHeadAlg Q Λ θ0 βs γs E x) n).trans
    (congrArg (fun y : TensorProductAlgebra k Q (Λ ∘ Fin.natAdd j)
      (singWeight (r + 1) (θ ∘ Fin.natAdd j)) ⊗[k] (AlgCat.of k (Hd ⊗[k] E) : AlgCat.{u} k) =>
      y • (singTailChain Q hQ j r Λ θ E Z).equiv n) (singTailOuter_apply Q j r Λ θ E x))

/-- **The right side of the inductive step**: the right side of the one-step associativity is
the partial standardization at the cut after the `j`-th red strand of the standardizations of
the two blocks. -/
def singStepTail := cutSpectTransport Q hQ (a := j) (r := r + 1) (Λ := Λ) (Λ' := Λ) rfl
    (rfl : θ0 = singWeight j (θ ∘ Fin.castAdd (r + 1)))
    (rfl : βs + γs = singWeight (r + 1) (θ ∘ Fin.natAdd j)) (AlgHom.id k E)
    (N := NN) (N' := (singOuter Q hQ j (r + 1) Λ θ E).obj Z)
    (singTailChain Q hQ j r Λ θ E Z).equiv (singTailChain_smul Q hQ j r Λ θ E Z)

/-- The standardization of all `j + r + 1` red strands, unfolded at the last red strand. -/
def singStepCross : IntertwiningEquiv (RingHom.id (TensorProductAlgebra k Q Λ
      (singWeight (j + (r + 1)) θ) ⊗[k] E))
    ((singStd Q hQ (j + (r + 1)) Λ θ E).obj
      ((ModuleCat.restrictScalars.{u} (singSplit Q j (r + 1) Λ θ E).toRingHom).obj Z))
    ((cutSpectFunctor (a := j + r) (r := 1) Q Λ (singWeight (j + r) θc) γs E hQ).obj
      (cutLastObj Q (j + r) Λ (singWeight (j + r) θc) γs E (singStepX Q hQ j r Λ θ E Z))) :=
  IntertwiningEquiv.ofObjEq rfl

/-- The casts of weights along the inductive step compose to the cast of weights. -/
theorem singStepCast_apply (t : TensorProductAlgebra k Q Λ (singWeight (j + (r + 1)) θ)) :
    castTensorProductAlgebra Q Λ (add_assoc θ0 βs γs)
        (castTensorProductAlgebra Q Λ (congrArg₂ (· + ·) (singWeight_add j r θc) (rfl : γs = γs))
          t) =
      castTensorProductAlgebra Q Λ (singWeight_add j (r + 1) θ) t :=
  castTensorProductAlgebra_comp Q Λ _ _ t

end Tail

/-- **The standardization with singleton blocks, split at a cut**: the standardization of all
`j + r` red strands is the partial standardization at the cut after the `j`-th red strand of
the standardizations of the two blocks, along the cast of weights. -/
def singCutEquiv (j : ℕ) : (r : ℕ) → (Λ : Fin (j + r) → I →₀ ℕ) →
    (θ : Fin (j + r) → Multiset I) → (E : AlgCat.{u} k) →
    (Z : ModuleCat.{u} (singAlg Q j (Λ ∘ Fin.castAdd r) (θ ∘ Fin.castAdd r) ⊗[k]
      (AlgCat.of k (singAlg Q r (Λ ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] E) :
        AlgCat.{u} k))) →
    IntertwiningEquiv (singWeightCast Q j r Λ θ E).toRingHom
      ((singStd Q hQ (j + r) Λ θ E).obj
        ((ModuleCat.restrictScalars.{u} (singSplit Q j r Λ θ E).toRingHom).obj Z))
      ((cutSpectFunctor (a := j) (r := r) Q Λ _ _ E hQ).obj ((singOuter Q hQ j r Λ θ E).obj Z))
  | 0, Λ, θ, E, Z => singCutEquivZero Q hQ j Λ θ E Z
  | r + 1, Λ, θ, E, Z =>
    ((((singStepCross Q hQ j r Λ θ E Z).trans
      (singStepSecond (singCutEquiv j r (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
        (cutLastSpect Q (j + r) Λ (θ (Fin.last (j + r))) E) (singStepZ Q j r Λ θ E Z)))).trans
      (singStepAssoc Q hQ j r Λ θ E Z)).trans (singStepTail Q hQ j r Λ θ E Z)).ofEq
      (fun x => by
        induction x using TensorProduct.inductionOn with
        | tmul t e => exact congrArg (· ⊗ₜ[k] e) (singStepCast_apply Q j r Λ θ t)
        | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans
            (map_add _ x y).symm))

end Categorification.Stendhal
