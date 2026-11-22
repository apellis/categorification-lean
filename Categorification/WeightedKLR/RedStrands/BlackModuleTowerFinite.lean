/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongFinite
import Categorification.Algebra.ModuleTower
import Categorification.WeightedKLR.RedStrands.BlackModuleTower
import Categorification.WeightedKLR.RedStrands.TensorFinite
import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# `Eᵢ` and `Fᵢ` on finitely generated modules along an `i`-string

Over a field, the tensor product algebras `T^λ` are finite-dimensional
(`tensorProductAlgebra_finite`), hence noetherian, and Webster's `Fᵢ` and `Eᵢ`
(arXiv:1309.3796v2, §4.6) preserve finite generation (`InductionAlong.Ind.finite`,
`InductionAlong.Res.finite`). So the functors `stringF`, `stringE` along an `i`-string
restrict to the abelian category `FGStringModules` of families of finitely generated modules,
with both adjunctions (`fgStringFEAdj`, and `fgStringEFAdj` at standard Khovanov–Lauda black
scalars). This is the abelian category of Chuang–Rouquier's weak `𝔰𝔩₂`-categorification along
one string (arXiv:math/0407205v2, §5.1.1).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u

section Generic

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ) {C : QuantumGroup.CartanDatum I}
  (hQ : KLR.IsRouquierQ C Q) (i : I) (ν₀ : Multiset I)

include hQ in
theorem tensorProductAlgebra_op_finite (ν : Multiset I) :
    Module.Finite k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ := by
  have := tensorProductAlgebra_finite Λ ν hQ
  exact Module.Finite.equiv (MulOpposite.opLinearEquiv k)

include hQ in
theorem isNoetherianRing_tensorProductAlgebra_op (ν : Multiset I) :
    IsNoetherianRing (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ := by
  have := tensorProductAlgebra_op_finite Λ hQ ν
  exact IsNoetherianRing.of_finite k _

theorem appendBlackOp_smul (ν : Multiset I) (c : k) (a : (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ) :
    appendBlackOp Q Λ i ν (c • a) = c • appendBlackOp Q Λ i ν a := by
  induction a using MulOpposite.rec' with
  | h x =>
    rw [← MulOpposite.op_smul, appendBlackOp_op, appendBlackOp_op, ← MulOpposite.op_smul]
    exact congrArg op ((appendBlack Q Λ i ν).map_smul' c x)

/-- The rings along the `i`-string. -/
abbrev StringAlg (m : ℕ) : Type u :=
  (TensorProductAlgebra k Q Λ (stringWeight i ν₀ m))ᵐᵒᵖ

include hQ in
theorem isNoetherianRing_stringAlg (m : ℕ) : IsNoetherianRing (StringAlg (Q := Q) Λ i ν₀ m) :=
  isNoetherianRing_tensorProductAlgebra_op Λ hQ _

/-- The finitely generated modules along the `i`-string. -/
abbrev FGStringModules :=
  ModuleTower.FGTower (StringAlg (Q := Q) Λ i ν₀)

theorem towerFinite_stringF (X : StringModules Q Λ i ν₀)
    (hX : ModuleTower.towerFinite (StringAlg (Q := Q) Λ i ν₀) X) :
    ModuleTower.towerFinite (StringAlg (Q := Q) Λ i ν₀) ((stringF Q Λ i ν₀).obj X) := by
  intro m
  cases m with
  | zero =>
    have : Subsingleton ((stringF Q Λ i ν₀).obj X 0) :=
      ModuleCat.subsingleton_of_isZero (Limits.isZero_zero _)
    exact ⟨⟨∅, Subsingleton.elim _ _⟩⟩
  | succ m =>
    have := hX m
    exact Ind.finite (N := X m) (φ := appendBlackOp Q Λ i (stringWeight i ν₀ m))

include hQ in
theorem towerFinite_stringE (X : StringModules Q Λ i ν₀)
    (hX : ModuleTower.towerFinite (StringAlg (Q := Q) Λ i ν₀) X) :
    ModuleTower.towerFinite (StringAlg (Q := Q) Λ i ν₀) ((stringE Q Λ i ν₀).obj X) := by
  intro m
  have : Module.Finite (TensorProductAlgebra k Q Λ ({i} + stringWeight i ν₀ m))ᵐᵒᵖ
      (PiShift.drop.obj X m) := hX (m + 1)
  have := tensorProductAlgebra_op_finite Λ hQ ({i} + stringWeight i ν₀ m)
  exact Res.finite k (appendBlackOp_smul Λ i _)

variable [∀ m, IsNoetherianRing (StringAlg (Q := Q) Λ i ν₀ m)]

/-- Webster's `Fᵢ` on finitely generated modules along the string. -/
abbrev fgStringF : FGStringModules (Q := Q) Λ i ν₀ ⥤ FGStringModules (Q := Q) Λ i ν₀ :=
  (ModuleTower.towerFinite _).lift ((ModuleTower.towerFinite _).ι ⋙ stringF Q Λ i ν₀)
    fun X => towerFinite_stringF Λ i ν₀ X.obj X.property

/-- Webster's `Eᵢ` on finitely generated modules along the string. -/
abbrev fgStringE : FGStringModules (Q := Q) Λ i ν₀ ⥤ FGStringModules (Q := Q) Λ i ν₀ :=
  (ModuleTower.towerFinite _).lift ((ModuleTower.towerFinite _).ι ⋙ stringE Q Λ i ν₀)
    fun X => towerFinite_stringE Λ hQ i ν₀ X.obj X.property

/-- `Fᵢ ⊣ Eᵢ` on finitely generated modules along the string. -/
def fgStringFEAdj : fgStringF Λ i ν₀ ⊣ fgStringE Λ hQ i ν₀ :=
  (stringFEAdj Q Λ i ν₀).restrictFullyFaithful
    (ModuleTower.towerFinite _).fullyFaithfulι (ModuleTower.towerFinite _).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

end Generic

section CL

open CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep
  CyclotomicAction DoubleDiagram KL3.Diagram

open scoped Classical

variable {I : Type u} {ℓ : ℕ} (i : I) (ν₀ : Multiset I) {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)

variable (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j)
  {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, u} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)

include hstd hP hwf in
/-- `Eᵢ ⊣ Fᵢ` on finitely generated modules along the string, at standard Khovanov–Lauda
black scalars (Webster, arXiv:1309.3796v3, Theorem 4.31). -/
def fgStringEFAdj (hR : KLR.IsRouquierQ C (CL.qCL KL))
    [∀ m, IsNoetherianRing (StringAlg (Q := CL.qCL KL) Λ i ν₀ m)] :
    fgStringE (k := k) (Q := CL.qCL KL) (C := C) Λ hR i ν₀ ⊣
      fgStringF (k := k) (Q := CL.qCL KL) Λ i ν₀ :=
  (stringEFAdj i ν₀ hstd hP hwf).restrictFullyFaithful
    (ModuleTower.towerFinite _).fullyFaithfulι (ModuleTower.towerFinite _).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

end CL

end Categorification.Stendhal
