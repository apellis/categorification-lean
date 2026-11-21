/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleEFTransport
import Categorification.WeightedKLR.RedStrands.BlackInductionExact

/-!
# The commutation relation of `Eᵢ` and `Fᵢ` on left modules over `T^λ`

The commutation relation of the categorical action (Webster, arXiv:1309.3796v3, Thm 4.31) on
all left modules over the tensor product algebra `T^λ` at standard Khovanov–Lauda black
scalars, an input of the dimension count in the proof of Proposition 5.5 there. A left module
is a right module through the horizontal reflection `tensorFlip` (`FlipView`), which commutes
with adding a black strand (`tensorFlip_appendBlack`); the statements on right modules
(`clBlackModuleEFEquiv`, `clBlackModuleFEEquiv`) transport along it. With `n = ⟨i, λ⟩` for `λ`
the right weight of content `i + ν`,

* `Eᵢ Fᵢ M ≅ Fᵢ Eᵢ M ⊕ M^{⊕ n}` when `n ≥ 0` (`clLeftBlackModuleEFEquiv`),
* `Fᵢ Eᵢ M ≅ Eᵢ Fᵢ M ⊕ M^{⊕ -n}` when `n ≤ 0` (`clLeftBlackModuleFEEquiv`),

as left `T^λ_{i+ν}`-modules, where `Fᵢ` is induction along `appendBlack` and `Eᵢ` is
restriction along it.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram InductionAlong MulOpposite

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u w

section Flip

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

/-- A left `T^λ_ν`-module, viewed as a right module through the horizontal reflection. -/
@[nolint unusedArguments]
def FlipView (_ : I → I → MvPolynomial (Fin 2) k) (_ : Fin ℓ → I →₀ ℕ) (_ : Multiset I)
    (M : Type w) : Type w := M

variable (ν : Multiset I) (M : Type w) [AddCommGroup M] [Module (TensorProductAlgebra k Q Λ ν) M]

instance : AddCommGroup (FlipView Q Λ ν M) := inferInstanceAs (AddCommGroup M)

instance : Module (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ (FlipView Q Λ ν M) :=
  Module.compHom M (tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν).symm.toRingHom

/-- The identity of `M`, from the left module to its reflected right-module view. -/
def toFlipView : M ≃+ FlipView Q Λ ν M := AddEquiv.refl M

theorem toFlipView_smul (t : TensorProductAlgebra k Q Λ ν) (m : M) :
    toFlipView Q Λ ν M (t • m) =
      tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν t • toFlipView Q Λ ν M m := by
  change t • m = (tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν).symm
    (tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν t) • m
  rw [RingEquiv.symm_apply_apply]

variable (i : I)

theorem appendBlackOp_tensorFlipRingEquiv (t : TensorProductAlgebra k Q Λ ν) :
    appendBlackOp Q Λ i ν (tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν t) =
      tensorFlipRingEquiv (Q := Q) (Λ := Λ) ((Singleton.singleton i : Multiset I) + ν)
        (appendBlackNU (Q := Q) (Λ := Λ) i ν t) := by
  change op (appendBlack Q Λ i ν (tensorFlip t)) = op (tensorFlip (appendBlack Q Λ i ν t))
  rw [tensorFlip_appendBlack]

end Flip

section Dimension

variable {k T : Type*} [Field k] [Ring T] [Algebra k T]
  {X Y M : Type*} [AddCommGroup X] [Module T X] [AddCommGroup Y] [Module T Y]
  [AddCommGroup M] [Module T M] {ι : Type*} [Fintype ι]

/-- The `k`-dimension form of a decomposition `X ≅ Y ⊕ M^ι` of modules over a `k`-algebra `T`,
with `k`-structures through `T`: `dim X = dim Y + |ι| dim M` when `Y`, `M` are
finite-dimensional. -/
theorem finrank_restrictScalars_eq_of_equiv_prod (L : X ≃ₗ[T] Y × (ι → M))
    [FiniteDimensional k (RestrictScalars k T Y)] [FiniteDimensional k (RestrictScalars k T M)] :
    Module.finrank k (RestrictScalars k T X) = Module.finrank k (RestrictScalars k T Y) +
      Fintype.card ι * Module.finrank k (RestrictScalars k T M) := by
  let e : RestrictScalars k T X ≃ₗ[k]
      RestrictScalars k T Y × (ι → RestrictScalars k T M) :=
    { toFun := fun x => L ((RestrictScalars.addEquiv k T X) x)
      invFun := fun y => (RestrictScalars.addEquiv k T X).symm (L.symm y)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by
        change L (algebraMap k T c • (RestrictScalars.addEquiv k T X) x) = _
        rw [L.map_smul]; rfl
      left_inv := fun x => by simp
      right_inv := fun y => by simp }
  rw [e.finrank_eq, Module.finrank_prod, Module.finrank_pi_fintype]
  simp

end Dimension

section CL

variable {I : Type u} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "RDc" => coordinateDatum Λ C
local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)
local notation "T" => TensorProductAlgebra k (CL.qCL KL) Λ

variable (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j)
  {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)
  (i : I) (ν : Multiset I)

local notation "Si" => (Singleton.singleton i : Multiset I)

variable (M : Type u) [AddCommGroup M]
  [Module (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ({i} + ν)) M]

local notation "FV" => FlipView (CL.qCL KL) Λ (Si + ν) M

/-- **`Eᵢ Fᵢ` against `Fᵢ Eᵢ` on left `T^λ`-modules** (Webster, arXiv:1309.3796v3, input of the
proof of Proposition 5.5): for `n = ⟨i, λ⟩ ≥ 0`, with `λ` the right weight of content `i + ν`,
`Eᵢ Fᵢ M ≅ Fᵢ Eᵢ M ⊕ M^{⊕ n}` for every left `T^λ_{i+ν}`-module `M`. -/
def clLeftBlackModuleEFEquiv (hn : 0 ≤ ip (RDc) i
      (downRightWeight (RDc) (coordinateRedWeights Λ C) (Si + ν))) :=
  resIndEquivTransport (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) ν)
    (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) (Si + ν))
    (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) (Si + (Si + ν)))
    (appendBlackOp_tensorFlipRingEquiv (CL.qCL KL) Λ ν i)
    (appendBlackOp_tensorFlipRingEquiv (CL.qCL KL) Λ (Si + ν) i)
    (toFlipView (CL.qCL KL) Λ (Si + ν) M) (toFlipView_smul (CL.qCL KL) Λ (Si + ν) M) _
    (clBlackModuleEFEquiv hstd hP hwf i ν FV hn)

/-- **`Fᵢ Eᵢ` against `Eᵢ Fᵢ` on left `T^λ`-modules** (Webster, arXiv:1309.3796v3, input of the
proof of Proposition 5.5): for `n = ⟨i, λ⟩ ≤ 0`, with `λ` the right weight of content `i + ν`,
`Fᵢ Eᵢ M ≅ Eᵢ Fᵢ M ⊕ M^{⊕ -n}` for every left `T^λ_{i+ν}`-module `M`. -/
def clLeftBlackModuleFEEquiv (hn : ip (RDc) i
      (downRightWeight (RDc) (coordinateRedWeights Λ C) (Si + ν)) ≤ 0) :=
  indResEquivTransport (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) ν)
    (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) (Si + ν))
    (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) (Si + (Si + ν)))
    (appendBlackOp_tensorFlipRingEquiv (CL.qCL KL) Λ ν i)
    (appendBlackOp_tensorFlipRingEquiv (CL.qCL KL) Λ (Si + ν) i)
    (toFlipView (CL.qCL KL) Λ (Si + ν) M) (toFlipView_smul (CL.qCL KL) Λ (Si + ν) M) _
    (clBlackModuleFEEquiv hstd hP hwf i ν FV hn)

end CL

end Categorification.Stendhal
