/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.CategoryTheory.PiShift
import Categorification.WeightedKLR.RedStrands.BlackModuleResIndAdjunction
import Categorification.WeightedKLR.RedStrands.TensorIntegrable

/-!
# `Eᵢ` and `Fᵢ` on the modules along an `i`-string

Fix a colour `i` and a weight `ν₀`. The weights `ν₀, {i} + ν₀, {i} + ({i} + ν₀), …`
(`stringWeight`) form the `i`-string through `ν₀`, and the right modules over the tensor
product algebras `T^λ` at these weights form the product category `StringModules`. Webster's
`Fᵢ` and `Eᵢ` (arXiv:1309.3796v2, §4.6) move along the string and assemble to endofunctors
`stringF`, `stringE` of it, adjoint on both sides at standard Khovanov–Lauda black scalars
(`stringFEAdj` from `Fᵢ ⊣ Eᵢ`, `stringEFAdj` from Theorem 4.31). This is the category of
Chuang–Rouquier's weak `𝔰𝔩₂`-categorification along one string (arXiv:math/0407205v2,
§5.1.1), used by Webster in §5. The string is finite: the algebras vanish far out
(`subsingleton_stringWeight`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory

/-- The weights along the `i`-string through `ν₀`: `ν₀` with `m` black strands of colour `i`
added. -/
def stringWeight {I : Type*} (i : I) (ν₀ : Multiset I) : ℕ → Multiset I
  | 0 => ν₀
  | m + 1 => {i} + stringWeight i ν₀ m

@[simp]
theorem stringWeight_zero {I : Type*} (i : I) (ν₀ : Multiset I) : stringWeight i ν₀ 0 = ν₀ :=
  rfl

theorem stringWeight_succ {I : Type*} (i : I) (ν₀ : Multiset I) (m : ℕ) :
    stringWeight i ν₀ (m + 1) = {i} + stringWeight i ν₀ m :=
  rfl

theorem stringWeight_eq {I : Type*} (i : I) (ν₀ : Multiset I) (m : ℕ) :
    stringWeight i ν₀ m = Multiset.replicate m i + ν₀ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [stringWeight_succ, ih, Multiset.replicate_succ, ← add_assoc]
    rfl

universe u

section Generic

variable {I : Type u} [DecidableEq I] {k : Type u} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν₀ : Multiset I)

/-- The modules along the `i`-string through `ν₀`: a right module over `T^λ` at each weight
`stringWeight i ν₀ m`. -/
abbrev StringModules :=
  ∀ m : ℕ, ModuleCat.{u} (TensorProductAlgebra k Q Λ (stringWeight i ν₀ m))ᵐᵒᵖ

/-- Webster's `Fᵢ` along the string: level `m` goes to level `m + 1`. -/
abbrev stringF : StringModules Q Λ i ν₀ ⥤ StringModules Q Λ i ν₀ :=
  PiShift.up fun m => blackF Q Λ i (stringWeight i ν₀ m)

/-- Webster's `Eᵢ` along the string: level `m + 1` goes to level `m`. -/
abbrev stringE : StringModules Q Λ i ν₀ ⥤ StringModules Q Λ i ν₀ :=
  PiShift.down fun m => blackE Q Λ i (stringWeight i ν₀ m)

/-- `Fᵢ ⊣ Eᵢ` along the string. -/
def stringFEAdj : stringF Q Λ i ν₀ ⊣ stringE Q Λ i ν₀ :=
  PiShift.upDownAdj fun m => blackAdjunction Q Λ i (stringWeight i ν₀ m)

/-- The string is finite: the tensor product algebras vanish far out along it. -/
theorem subsingleton_stringWeight {C : QuantumGroup.CartanDatum I} (hQ : KLR.IsRouquierQ C Q) :
    ∃ B : ℕ, ∀ m ≥ B, Subsingleton (TensorProductAlgebra k Q Λ (stringWeight i ν₀ m)) := by
  obtain ⟨B, hB⟩ := eventually_subsingleton_tensor Λ hQ i ν₀
  exact ⟨B, fun m hm => stringWeight_eq i ν₀ m ▸ hB m hm⟩

end Generic

section CL

open CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep
  CyclotomicAction DoubleDiagram KL3.Diagram

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type u} {ℓ : ℕ} (i : I) (ν₀ : Multiset I) {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "RDc" => coordinateDatum Λ C
local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)

variable (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j)
  {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, u} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)

/-- `Eᵢ ⊣ Fᵢ` along the string, at standard Khovanov–Lauda black scalars (Webster,
arXiv:1309.3796v3, Theorem 4.31). -/
def stringEFAdj :
    stringE (CL.qCL KL) Λ i ν₀ ⊣ stringF (CL.qCL KL) Λ i ν₀ :=
  PiShift.downUpAdj fun m => clBlackResIndAdjunction hstd hP hwf i (stringWeight i ν₀ m)

end CL

end Categorification.Stendhal
