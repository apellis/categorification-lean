/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleEFOutsideContent
import Categorification.WeightedKLR.RedStrands.ResIndPiTransport
import Categorification.WeightedKLR.RedStrands.BlackModuleEFLeftNaturality

/-!
# `Eᵢ Fᵢ` on modules over `T^λ` of a weight not containing `i`

For a colour `i` outside the black content `μ`, `Eᵢ` vanishes on modules over the tensor product
algebra `T^λ_μ` and the commutation relation of the categorical action (Webster,
arXiv:1309.3796v3, Thm 4.31, used in the dimension count of the proof of Proposition 5.5) reads
`Eᵢ Fᵢ M ≅ M^{⊕ n}` with `n = ⟨i, λ⟩ ≥ 0`, for `λ` the right weight of content `μ`. At standard
Khovanov–Lauda black scalars:

* `clBlackModuleEFEquivOfNotMem`, `clBlackModuleEFEquivOfNotMem_map`: right modules;
* `clLeftBlackModuleEFEquivOfNotMem`, `clLeftBlackModuleEFEquivOfNotMem_map`: left modules;
* `finrank_clLeftEF_eq_of_notMem`: `dim Eᵢ Fᵢ M = n dim M` over `k`.

They are transported from the all-down matrix ring (`blackModuleEFEquivOfNotMem`) through the
repaired Lemma 4.29 (`clOpEquiv`) and the horizontal reflection (`tensorFlipRingEquiv`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram InductionAlong MulOpposite

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Dimension

variable {k T : Type*} [Field k] [Ring T] [Algebra k T]
  {X M : Type*} [AddCommGroup X] [Module T X] [AddCommGroup M] [Module T M]
  {ι : Type*} [Fintype ι]

/-- The `k`-dimension form of an isomorphism `X ≅ M^ι` of modules over a `k`-algebra `T`,
with `k`-structures through `T`: `dim X = |ι| dim M` when `M` is finite-dimensional. -/
theorem finrank_restrictScalars_eq_of_equiv_pi (L : X ≃ₗ[T] (ι → M))
    [FiniteDimensional k (RestrictScalars k T M)] :
    Module.finrank k (RestrictScalars k T X) =
      Fintype.card ι * Module.finrank k (RestrictScalars k T M) := by
  let e : RestrictScalars k T X ≃ₗ[k] (ι → RestrictScalars k T M) :=
    { toFun := fun x => L ((RestrictScalars.addEquiv k T X) x)
      invFun := fun y => (RestrictScalars.addEquiv k T X).symm (L.symm y)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by
        change L (algebraMap k T c • (RestrictScalars.addEquiv k T X) x) = _
        rw [L.map_smul]; rfl
      left_inv := fun x => by simp
      right_inv := fun y => by simp }
  rw [e.finrank_eq, Module.finrank_pi_fintype]
  simp

end Dimension

section CL

universe u w

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
  (i : I) (μ : Multiset I)

local notation "PD" => clDownwardBlock Λ C P

local notation "Pin" => addDownRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C)
  (affineCoverQ (clDownwardQ KL) Λ) (signedCapKLPresentation (RDc)
    (redWeight (cyclotomicCoverWeightDatum Λ C)) P (clDownwardQ KL) Λ fun _ _ => 1)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "nᵢ" => ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) μ)

/-- A right `T^λ_μ`-module `M`, viewed as a module over the all-down matrix ring through the
repaired Lemma 4.29 (`clOpEquiv`). -/
@[nolint unusedArguments]
def ClMatViewOf (_ : ∀ i j, i ≠ j → Q i j = CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j)
    (_ : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
      (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
        I ⊕ Fin ℓ → ℤ) P)
    (_ : P.WFDom) (_ : Multiset I) (M : Type u) : Type u := M

section View

variable (M : Type u) [AddCommGroup M]
  [Module (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ μ)ᵐᵒᵖ M]

instance : AddCommGroup (ClMatViewOf hstd hP hwf μ M) := inferInstanceAs (AddCommGroup M)

instance : Module (downwardMatrix (PD) μ)ᵐᵒᵖ (ClMatViewOf hstd hP hwf μ M) :=
  Module.compHom M (clOpEquiv hstd hP hwf μ).symm.toRingHom

/-- The identity of `M`, from `T^λ_μ` to its matrix-ring view. -/
def toClMatViewOf : M ≃+ ClMatViewOf hstd hP hwf μ M := AddEquiv.refl M

theorem toClMatViewOf_smul (t : (TensorProductAlgebra k (CL.qCL KL) Λ μ)ᵐᵒᵖ) (m : M) :
    toClMatViewOf hstd hP hwf μ M (t • m) =
      clOpEquiv hstd hP hwf μ t • toClMatViewOf hstd hP hwf μ M m := by
  change t • m = (clOpEquiv hstd hP hwf μ).symm (clOpEquiv hstd hP hwf μ t) • m
  rw [RingEquiv.symm_apply_apply]

/-- **`Eᵢ Fᵢ` on `T^λ_μ`-modules for `i ∉ μ`** (Webster, arXiv:1309.3796v3, Thm 4.31 with
`Eᵢ M = 0`, input of the proof of Proposition 5.5): `Eᵢ Fᵢ M ≅ M^{⊕ n}` with `n = ⟨i, λ⟩`, for
every right `T^λ_μ`-module `M`. Transported from the all-down matrix ring
(`blackModuleEFEquivOfNotMem`) through the repaired Lemma 4.29. -/
def clBlackModuleEFEquivOfNotMem (hi : i ∉ μ) :
    Res (appendBlackOp (CL.qCL KL) Λ i μ) (Ind M (appendBlackOp (CL.qCL KL) Λ i μ)) ≃ₗ[(T μ)ᵐᵒᵖ]
      (Fin (nᵢ).toNat → M) :=
  resIndPiEquivTransport (clOpEquiv hstd hP hwf μ) (clOpEquiv hstd hP hwf (Si + μ))
    (clOpEquiv_appendBlack hstd hP hwf i μ) (toClMatViewOf hstd hP hwf μ M)
    (toClMatViewOf_smul hstd hP hwf μ M) _
    (blackModuleEFEquivOfNotMem (Pin) (KL).t i μ (clDownwardBlock_reflectedBlack P)
      (ClMatViewOf hstd hP hwf μ M) hi)

end View

section Naturality

variable {M M₂ : Type u} [AddCommGroup M] [AddCommGroup M₂]
  [Module (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ μ)ᵐᵒᵖ M]
  [Module (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ μ)ᵐᵒᵖ M₂]

/-- A module map of right `T^λ_μ`-modules, as a map of their matrix-ring views. -/
def clMatViewOfMap (f : M →ₗ[(T μ)ᵐᵒᵖ] M₂) :
    ClMatViewOf hstd hP hwf μ M →ₗ[(downwardMatrix (PD) μ)ᵐᵒᵖ] ClMatViewOf hstd hP hwf μ M₂ where
  toFun := f
  map_add' := f.map_add
  map_smul' t m := f.map_smul ((clOpEquiv hstd hP hwf μ).symm t) m

/-- **Naturality of `clBlackModuleEFEquivOfNotMem`**: it carries `Eᵢ Fᵢ f` to `f^n`. -/
theorem clBlackModuleEFEquivOfNotMem_map (f : M →ₗ[(T μ)ᵐᵒᵖ] M₂) (hi : i ∉ μ)
    (x : Res (appendBlackOp (CL.qCL KL) Λ i μ) (Ind M (appendBlackOp (CL.qCL KL) Λ i μ))) :
    clBlackModuleEFEquivOfNotMem hstd hP hwf i μ M₂ hi (Res.map (Ind.map f) x) =
      fun s => f (clBlackModuleEFEquivOfNotMem hstd hP hwf i μ M hi x s) := by
  kernel_exact resIndPiEquivTransport_map (clOpEquiv hstd hP hwf μ)
    (clOpEquiv hstd hP hwf (Si + μ)) (clOpEquiv_appendBlack hstd hP hwf i μ)
    (toClMatViewOf hstd hP hwf μ M) (toClMatViewOf_smul hstd hP hwf μ M)
    (toClMatViewOf hstd hP hwf μ M₂) (toClMatViewOf_smul hstd hP hwf μ M₂)
    f (clMatViewOfMap hstd hP hwf μ f) (fun _ => rfl) _
    (blackModuleEFEquivOfNotMem (Pin) (KL).t i μ (clDownwardBlock_reflectedBlack P)
      (ClMatViewOf hstd hP hwf μ M) hi)
    (blackModuleEFEquivOfNotMem (Pin) (KL).t i μ (clDownwardBlock_reflectedBlack P)
      (ClMatViewOf hstd hP hwf μ M₂) hi)
    (fun y => by
      kernel_exact blackModuleEFEquivOfNotMem_map (Pin) (KL).t i μ
        (clDownwardBlock_reflectedBlack P) (clMatViewOfMap hstd hP hwf μ f) hi y) x

end Naturality

local notation "ψμ" => appendBlackNU (Q := CL.qCL KL) (Λ := Λ) i μ

section Left

variable (M : Type u) [AddCommGroup M]
  [Module (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ μ) M]

/-- **`Eᵢ Fᵢ` on left `T^λ_μ`-modules for `i ∉ μ`** (Webster, arXiv:1309.3796v3, Thm 4.31 with
`Eᵢ M = 0`, input of the proof of Proposition 5.5): `Eᵢ Fᵢ M ≅ M^{⊕ n}` with `n = ⟨i, λ⟩`, for
every left `T^λ_μ`-module `M`. -/
def clLeftBlackModuleEFEquivOfNotMem (hi : i ∉ μ) :
    Res (ψμ) (Ind M (ψμ)) ≃ₗ[T μ] (Fin (nᵢ).toNat → M) :=
  resIndPiEquivTransport (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) μ)
    (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) (Si + μ))
    (appendBlackOp_tensorFlipRingEquiv (CL.qCL KL) Λ μ i)
    (toFlipView (CL.qCL KL) Λ μ M) (toFlipView_smul (CL.qCL KL) Λ μ M) _
    (clBlackModuleEFEquivOfNotMem hstd hP hwf i μ (FlipView (CL.qCL KL) Λ μ M) hi)

end Left

section LeftNaturality

variable {M M₂ : Type u} [AddCommGroup M] [AddCommGroup M₂]
  [Module (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ μ) M]
  [Module (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ μ) M₂]

/-- **Naturality of `clLeftBlackModuleEFEquivOfNotMem`**: it carries `Eᵢ Fᵢ f` to `f^n`. -/
theorem clLeftBlackModuleEFEquivOfNotMem_map (f : M →ₗ[T μ] M₂) (hi : i ∉ μ)
    (x : Res (ψμ) (Ind M (ψμ))) :
    clLeftBlackModuleEFEquivOfNotMem hstd hP hwf i μ M₂ hi (Res.map (Ind.map f) x) =
      fun s => f (clLeftBlackModuleEFEquivOfNotMem hstd hP hwf i μ M hi x s) := by
  kernel_exact resIndPiEquivTransport_map (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) μ)
    (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) (Si + μ))
    (appendBlackOp_tensorFlipRingEquiv (CL.qCL KL) Λ μ i)
    (toFlipView (CL.qCL KL) Λ μ M) (toFlipView_smul (CL.qCL KL) Λ μ M)
    (toFlipView (CL.qCL KL) Λ μ M₂) (toFlipView_smul (CL.qCL KL) Λ μ M₂)
    f (flipViewMap (CL.qCL KL) Λ μ f) (fun _ => rfl) _
    (clBlackModuleEFEquivOfNotMem hstd hP hwf i μ (FlipView (CL.qCL KL) Λ μ M) hi)
    (clBlackModuleEFEquivOfNotMem hstd hP hwf i μ (FlipView (CL.qCL KL) Λ μ M₂) hi)
    (fun y => by
      kernel_exact clBlackModuleEFEquivOfNotMem_map hstd hP hwf i μ
        (flipViewMap (CL.qCL KL) Λ μ f) hi y) x

end LeftNaturality

section Dim

variable (M : Type u) [AddCommGroup M]
  [Module (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ μ) M]

local notation "EF" => InductionAlong.Res (ψμ) (InductionAlong.Ind M (ψμ))

include hstd hP hwf in
/-- **The dimension form of `Eᵢ Fᵢ M ≅ M^{⊕ n}` for `i ∉ μ`** on finite-dimensional left
`T^λ_μ`-modules (Webster, arXiv:1309.3796v3, Thm 4.31 with `Eᵢ M = 0`, input of the dimension
count in the proof of Proposition 5.5): `dim Eᵢ Fᵢ M = n dim M` with `n = ⟨i, λ⟩ ≥ 0`,
dimensions over `k`. -/
theorem finrank_clLeftEF_eq_of_notMem (hi : i ∉ μ)
    [FiniteDimensional k (RestrictScalars k (T μ) M)] :
    (Module.finrank k (RestrictScalars k (T μ) EF) : ℤ) =
      nᵢ * Module.finrank k (RestrictScalars k (T μ) M) := by
  have e := finrank_restrictScalars_eq_of_equiv_pi (k := k)
    (clLeftBlackModuleEFEquivOfNotMem hstd hP hwf i μ M hi)
  rw [e, Fintype.card_fin]
  push_cast
  rw [Int.toNat_of_nonneg (ip_nonneg_of_notMem i μ hi)]

end Dim

end CL

end Categorification.Stendhal
