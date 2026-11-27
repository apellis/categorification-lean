/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleEFOutsideContentCL
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackActionQ
import Categorification.WeightedKLR.RedStrands.BlackModuleEFOutsideContentQ
import Categorification.WeightedKLR.RedStrands.ResIndPiTransport
import Categorification.WeightedKLR.RedStrands.BlackModuleEFLeftNaturalityQ

/-!
# `Eᵢ Fᵢ` on modules over `T^λ` of a weight not containing `i`

For a colour `i` outside the black content `μ`, `Eᵢ` vanishes on modules over the tensor product
algebra `T^λ_μ` and the commutation relation of the categorical action (Webster,
arXiv:1309.3796v3, Thm 4.31, used in the dimension count of the proof of Proposition 5.5) reads
`Eᵢ Fᵢ M ≅ M^{⊕ n}` with `n = ⟨i, λ⟩ ≥ 0`, for `λ` the right weight of content `μ`. At standard
Khovanov–Lauda black scalars:

* `clBlackModuleEFEquivOfNotMemQ`, `clBlackModuleEFEquivOfNotMem_mapQ`: right modules;
* `clLeftBlackModuleEFEquivOfNotMemQ`, `clLeftBlackModuleEFEquivOfNotMem_mapQ`: left modules;
* `finrank_clLeftEF_eq_of_notMemQ`: `dim Eᵢ Fᵢ M = n dim M` over `k`.

They are transported from the all-down matrix ring (`blackModuleEFEquivOfNotMemQ`) through the
repaired Lemma 4.29 (`clOpEquivQ`) and the horizontal reflection (`tensorFlipRingEquiv`).

This is the version of `BlackModuleEFOutsideContentCL` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
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

end Dimension

section CL

universe u w

variable {I : Type u} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "RDc" => coordinateDatum Λ C
local notation "KL" => blackScalarsQ Λ C hQ
local notation "T" => TensorProductAlgebra k (Q) Λ

variable {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)
  (i : I) (μ : Multiset I)

local notation "PD" => clDownwardBlockQ Λ C hQ P

local notation "Pin" => addDownRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C)
  (affineCoverQ (clDownwardQ KL) Λ) (signedCapPresentationOf (RDc) (redWeight (cyclotomicCoverWeightDatum Λ C)) (CLQ.pres (RDc) k KL) P (clDownwardQ KL) Λ fun i j => (CL.CLScalars.t KL i j : k))

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "nᵢ" => ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) μ)

/-- A right `T^λ_μ`-module `M`, viewed as a module over the all-down matrix ring through the
repaired Lemma 4.29 (`clOpEquivQ`). -/
@[nolint unusedArguments]
def ClMatViewOfQ (_ : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
      (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
        I ⊕ Fin ℓ → ℤ) P)
    (_ : P.WFDom) (_ : Multiset I) (M : Type u) : Type u := M

section View

variable (M : Type u) [AddCommGroup M]
  [Module (TensorProductAlgebra k (Q) Λ μ)ᵐᵒᵖ M]

instance : AddCommGroup (ClMatViewOfQ hP hwf μ M) := inferInstanceAs (AddCommGroup M)

instance : Module (downwardMatrix (PD) μ)ᵐᵒᵖ (ClMatViewOfQ hP hwf μ M) :=
  Module.compHom M (clOpEquivQ hP hwf μ).symm.toRingHom

/-- The identity of `M`, from `T^λ_μ` to its matrix-ring view. -/
def toClMatViewOfQ : M ≃+ ClMatViewOfQ hP hwf μ M := AddEquiv.refl M

theorem toClMatViewOf_smulQ (t : (TensorProductAlgebra k (Q) Λ μ)ᵐᵒᵖ) (m : M) :
    toClMatViewOfQ hP hwf μ M (t • m) =
      clOpEquivQ hP hwf μ t • toClMatViewOfQ hP hwf μ M m := by
  change t • m = (clOpEquivQ hP hwf μ).symm (clOpEquivQ hP hwf μ t) • m
  rw [RingEquiv.symm_apply_apply]

/-- **`Eᵢ Fᵢ` on `T^λ_μ`-modules for `i ∉ μ`** (Webster, arXiv:1309.3796v3, Thm 4.31 with
`Eᵢ M = 0`, input of the proof of Proposition 5.5): `Eᵢ Fᵢ M ≅ M^{⊕ n}` with `n = ⟨i, λ⟩`, for
every right `T^λ_μ`-module `M`. Transported from the all-down matrix ring
(`blackModuleEFEquivOfNotMemQ`) through the repaired Lemma 4.29. -/
def clBlackModuleEFEquivOfNotMemQ (hi : i ∉ μ) :
    Res (appendBlackOp (Q) Λ i μ) (Ind M (appendBlackOp (Q) Λ i μ)) ≃ₗ[(T μ)ᵐᵒᵖ]
      (Fin (nᵢ).toNat → M) :=
  resIndPiEquivTransport (clOpEquivQ hP hwf μ) (clOpEquivQ hP hwf (Si + μ))
    (clOpEquiv_appendBlackQ hP hwf i μ) (toClMatViewOfQ hP hwf μ M)
    (toClMatViewOf_smulQ hP hwf μ M) _
    (blackModuleEFEquivOfNotMemQ (Pin) (CL.CLScalars.t KL) i μ (clDownwardBlockQ_reflectedBlack P)
      (ClMatViewOfQ hP hwf μ M) hi)

end View

section Naturality

variable {M M₂ : Type u} [AddCommGroup M] [AddCommGroup M₂]
  [Module (TensorProductAlgebra k (Q) Λ μ)ᵐᵒᵖ M]
  [Module (TensorProductAlgebra k (Q) Λ μ)ᵐᵒᵖ M₂]

/-- A module map of right `T^λ_μ`-modules, as a map of their matrix-ring views. -/
def clMatViewOfMapQ (f : M →ₗ[(T μ)ᵐᵒᵖ] M₂) :
    ClMatViewOfQ hP hwf μ M →ₗ[(downwardMatrix (PD) μ)ᵐᵒᵖ] ClMatViewOfQ hP hwf μ M₂ where
  toFun := f
  map_add' := f.map_add
  map_smul' t m := f.map_smul ((clOpEquivQ hP hwf μ).symm t) m

/-- **Naturality of `clBlackModuleEFEquivOfNotMemQ`**: it carries `Eᵢ Fᵢ f` to `f^n`. -/
theorem clBlackModuleEFEquivOfNotMem_mapQ (f : M →ₗ[(T μ)ᵐᵒᵖ] M₂) (hi : i ∉ μ)
    (x : Res (appendBlackOp (Q) Λ i μ) (Ind M (appendBlackOp (Q) Λ i μ))) :
    clBlackModuleEFEquivOfNotMemQ hP hwf i μ M₂ hi (Res.map (Ind.map f) x) =
      fun s => f (clBlackModuleEFEquivOfNotMemQ hP hwf i μ M hi x s) := by
  kernel_exact resIndPiEquivTransport_map (clOpEquivQ hP hwf μ)
    (clOpEquivQ hP hwf (Si + μ)) (clOpEquiv_appendBlackQ hP hwf i μ)
    (toClMatViewOfQ hP hwf μ M) (toClMatViewOf_smulQ hP hwf μ M)
    (toClMatViewOfQ hP hwf μ M₂) (toClMatViewOf_smulQ hP hwf μ M₂)
    f (clMatViewOfMapQ hP hwf μ f) (fun _ => rfl) _
    (blackModuleEFEquivOfNotMemQ (Pin) (CL.CLScalars.t KL) i μ (clDownwardBlockQ_reflectedBlack P)
      (ClMatViewOfQ hP hwf μ M) hi)
    (blackModuleEFEquivOfNotMemQ (Pin) (CL.CLScalars.t KL) i μ (clDownwardBlockQ_reflectedBlack P)
      (ClMatViewOfQ hP hwf μ M₂) hi)
    (fun y => by
      kernel_exact blackModuleEFEquivOfNotMem_mapQ (Pin) (CL.CLScalars.t KL) i μ
        (clDownwardBlockQ_reflectedBlack P) (clMatViewOfMapQ hP hwf μ f) hi y) x

end Naturality

local notation "ψμ" => appendBlackNU (Q := Q) (Λ := Λ) i μ

section Left

variable (M : Type u) [AddCommGroup M]
  [Module (TensorProductAlgebra k (Q) Λ μ) M]

/-- **`Eᵢ Fᵢ` on left `T^λ_μ`-modules for `i ∉ μ`** (Webster, arXiv:1309.3796v3, Thm 4.31 with
`Eᵢ M = 0`, input of the proof of Proposition 5.5): `Eᵢ Fᵢ M ≅ M^{⊕ n}` with `n = ⟨i, λ⟩`, for
every left `T^λ_μ`-module `M`. -/
def clLeftBlackModuleEFEquivOfNotMemQ (hi : i ∉ μ) :
    Res (ψμ) (Ind M (ψμ)) ≃ₗ[T μ] (Fin (nᵢ).toNat → M) :=
  resIndPiEquivTransport (tensorFlipRingEquiv (Q := Q) (Λ := Λ) μ)
    (tensorFlipRingEquiv (Q := Q) (Λ := Λ) (Si + μ))
    (appendBlackOp_tensorFlipRingEquiv (Q) Λ μ i)
    (toFlipView (Q) Λ μ M) (toFlipView_smul (Q) Λ μ M) _
    (clBlackModuleEFEquivOfNotMemQ hP hwf i μ (FlipView (Q) Λ μ M) hi)

end Left

section LeftNaturality

variable {M M₂ : Type u} [AddCommGroup M] [AddCommGroup M₂]
  [Module (TensorProductAlgebra k (Q) Λ μ) M]
  [Module (TensorProductAlgebra k (Q) Λ μ) M₂]

/-- **Naturality of `clLeftBlackModuleEFEquivOfNotMemQ`**: it carries `Eᵢ Fᵢ f` to `f^n`. -/
theorem clLeftBlackModuleEFEquivOfNotMem_mapQ (f : M →ₗ[T μ] M₂) (hi : i ∉ μ)
    (x : Res (ψμ) (Ind M (ψμ))) :
    clLeftBlackModuleEFEquivOfNotMemQ hP hwf i μ M₂ hi (Res.map (Ind.map f) x) =
      fun s => f (clLeftBlackModuleEFEquivOfNotMemQ hP hwf i μ M hi x s) := by
  kernel_exact resIndPiEquivTransport_map (tensorFlipRingEquiv (Q := Q) (Λ := Λ) μ)
    (tensorFlipRingEquiv (Q := Q) (Λ := Λ) (Si + μ))
    (appendBlackOp_tensorFlipRingEquiv (Q) Λ μ i)
    (toFlipView (Q) Λ μ M) (toFlipView_smul (Q) Λ μ M)
    (toFlipView (Q) Λ μ M₂) (toFlipView_smul (Q) Λ μ M₂)
    f (flipViewMap (Q) Λ μ f) (fun _ => rfl) _
    (clBlackModuleEFEquivOfNotMemQ hP hwf i μ (FlipView (Q) Λ μ M) hi)
    (clBlackModuleEFEquivOfNotMemQ hP hwf i μ (FlipView (Q) Λ μ M₂) hi)
    (fun y => by
      kernel_exact clBlackModuleEFEquivOfNotMem_mapQ hP hwf i μ
        (flipViewMap (Q) Λ μ f) hi y) x

end LeftNaturality

section Dim

variable (M : Type u) [AddCommGroup M]
  [Module (TensorProductAlgebra k (Q) Λ μ) M]

local notation "EF" => InductionAlong.Res (ψμ) (InductionAlong.Ind M (ψμ))

include hP hwf in
/-- **The dimension form of `Eᵢ Fᵢ M ≅ M^{⊕ n}` for `i ∉ μ`** on finite-dimensional left
`T^λ_μ`-modules (Webster, arXiv:1309.3796v3, Thm 4.31 with `Eᵢ M = 0`, input of the dimension
count in the proof of Proposition 5.5): `dim Eᵢ Fᵢ M = n dim M` with `n = ⟨i, λ⟩ ≥ 0`,
dimensions over `k`. -/
theorem finrank_clLeftEF_eq_of_notMemQ (hi : i ∉ μ)
    [FiniteDimensional k (RestrictScalars k (T μ) M)] :
    (Module.finrank k (RestrictScalars k (T μ) EF) : ℤ) =
      nᵢ * Module.finrank k (RestrictScalars k (T μ) M) := by
  have e := finrank_restrictScalars_eq_of_equiv_pi (k := k)
    (clLeftBlackModuleEFEquivOfNotMemQ hP hwf i μ M hi)
  rw [e, Fintype.card_fin]
  push_cast
  rw [Int.toNat_of_nonneg (ip_nonneg_of_notMem i μ hi)]

end Dim

end CL

end Categorification.Stendhal
