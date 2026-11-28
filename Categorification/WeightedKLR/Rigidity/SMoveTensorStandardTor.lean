/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveStandardTor
import Categorification.WeightedKLR.RedStrands.BraidedOrderedStandardResolution
import Categorification.Algebra.DerivedTensorRingEquiv

/-!
# Tor between standard-filtered modules over the tensor product algebra

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22. The partial standardizations of the S-move are left modules over
`T = T^{λ ∘ σ}` filtered by the left standards `leftStandard`, while the vanishing of the `E²`
terms is proved over the braid corner `C` between right loading standards `S_t` and reflected
loading standards `Ṡ_s` (`isZero_derivedTensorHomology_of_loadingFiltrations`).

The ring isomorphism `φ : C ≃ T` (`reflectedLeftCoefficientEquiv`, the corner flip followed by
the coefficient equivalence) carries `Ṡ_s` to the left standard `leftStandard s`
(`reflectedLoadingStandardLeftEquiv`). The right standards of `T` are taken to be the right
loading standards `S_t` transported along `φ` (`tensorRightStandard`). Tor over `T` is Tor over
`C` (`isZero_derivedTensorHomology_of_ringEquiv`), so the corner statements hold over `T`.

## Main definitions

* `tensorRightStandard`: the right standard `S_t` as a right `T`-module.

## Main results

* `isZero_derivedTensorHomology_tensor_of_standardFiltrations`: no Tor between a right module
  filtered by `S_t` and a left module filtered by left standards, when no two labels are
  equivalent.
* `isZero_derivedTensorHomology_tensor_of_standardFiltrations_of_ne_zero`: higher Tor vanish.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory CategoryTheory.Limits KLR Equiv MulOpposite CornerEndomorphism DG
open DG.DerivedCategory
open scoped DG.DegreeZero

universe w

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q) (σ : Perm (Fin ℓ))

local notation "κ" => List.map σ (List.finRange ℓ)
local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ
local notation "T" => TensorProductAlgebra k Q (Λ ∘ σ) ν
local notation "μ" => stendhalWeight ℓ ν
local notation "φ" => reflectedLeftCoefficientEquiv (Λ := Λ) hρ hQ σ

/-- **The right standard `S_t` of `T`**: the right loading standard of the corner, as a right
`T`-module through `φ : C ≃ T`. -/
abbrev tensorRightStandard (t : Seq μ) :
    ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ σ) ν)ᵐᵒᵖ :=
  (ModuleCat.restrictScalars (RingHom.op (φ).symm.toRingHom)).obj
    (ModuleCat.of Cᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ t) κ))

/-- Transporting `S_t` back to the corner gives `S_t`. -/
def tensorRightStandardCoefficientEquiv (t : Seq μ) :
    (ModuleCat.restrictScalars (RingHom.op (φ).symm.symm.toRingHom)).obj
        (tensorRightStandard (Λ := Λ) (ν := ν) hρ hQ σ t) ≃ₗ[Cᵐᵒᵖ]
      ModuleCat.of Cᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ t) κ) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' c x := by
    rw [RingHom.id_apply]
    exact congrArg (fun a : Cᵐᵒᵖ =>
      a • (show ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ t) κ from x))
      (show op ((φ).symm ((φ).symm.symm c.unop)) = c by
        rw [RingEquiv.symm_symm, RingEquiv.symm_apply_apply]; rfl)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Restricting the left standard to the corner gives the reflected loading standard. -/
def restrictLeftStandardEquiv {s : Seq μ} (hs : IsRedOrdered s) :
    (ModuleCat.restrictScalars (φ).symm.symm.toRingHom).obj
        (ModuleCat.of T (leftStandard Q (Λ ∘ σ) s hs)) ≃ₗ[C]
      ReflectedLoadingStandard (k := k) (Q := Q) (Λ := Λ) σ s where
  toEquiv := (reflectedLoadingStandardLeftEquiv (Λ := Λ) hρ hQ σ hs).toEquiv.symm
  map_add' x y := (reflectedLoadingStandardLeftEquiv (Λ := Λ) hρ hQ σ hs).symm.map_add x y
  map_smul' c x := by
    let e := reflectedLoadingStandardLeftEquiv (Λ := Λ) hρ hQ σ hs
    change e.symm ((φ c) • (show leftStandard Q (Λ ∘ σ) s hs from x)) = c • e.symm x
    refine (e.symm.map_smulₛₗ (φ c) x).trans ?_
    congr 1
    exact (φ).symm_apply_apply c


/-- A right `T`-module, restricted to the corner, is its derived-tensor coefficient. -/
def restrictCoefficientEquiv (N : ModuleCat.{0} Tᵐᵒᵖ) :
    (ModuleCat.restrictScalars (RingHom.op (φ).symm.symm.toRingHom)).obj N ≃ₗ[Cᵐᵒᵖ]
      ringEquivCoefficient (φ).symm N where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Transport a filtration by right standards over `T` to the corner. -/
theorem corner_filtration_right {m : List {s : Seq μ // IsRedOrdered s}}
    {N : ModuleCat.{0} Tᵐᵒᵖ}
    (hN : ModuleFiltration.HasFiltration
      (fun t : {s : Seq μ // IsRedOrdered s} =>
        tensorRightStandard (Λ := Λ) (ν := ν) hρ hQ σ t.1) m N) :
    ModuleFiltration.HasFiltration (fun t : {s : Seq μ // IsRedOrdered s} =>
        ModuleCat.of Cᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ t.1) κ))
        m (ringEquivCoefficient (φ).symm N) := by
  have h₁ := hN.restrictScalars (RingHom.op (φ).symm.symm.toRingHom)
  have h₂ := h₁.mono (L' := fun t : {s : Seq μ // IsRedOrdered s} =>
    ModuleCat.of Cᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ t.1) κ))
    fun t => ⟨tensorRightStandardCoefficientEquiv hρ hQ σ t.1⟩
  exact h₂.of_equiv (restrictCoefficientEquiv hρ hQ σ N)

/-- Transport a filtration by left standards over `T` to the corner. -/
theorem corner_filtration_left {m' : List {s : Seq μ // IsRedOrdered s}} {Y : ModuleCat.{0} T}
    (hY : ModuleFiltration.HasFiltration (fun s : {s : Seq μ // IsRedOrdered s} =>
      ModuleCat.of T (leftStandard Q (Λ ∘ σ) s.1 s.2)) m' Y) :
    ModuleFiltration.HasFiltration (fun s : {s : Seq μ // IsRedOrdered s} =>
        ReflectedLoadingStandard (k := k) (Q := Q) (Λ := Λ) σ s.1) m'
        ((ModuleCat.restrictScalars (φ).symm.symm.toRingHom).obj Y) := by
  have h₁ := hY.restrictScalars (φ).symm.symm.toRingHom
  exact h₁.mono (L' := fun s : {s : Seq μ // IsRedOrdered s} =>
    ReflectedLoadingStandard (k := k) (Q := Q) (Λ := Λ) σ s.1)
    fun s => ⟨restrictLeftStandardEquiv hρ hQ σ s.2⟩

variable [HasDerivedCategory.{w, 0}
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) (List.map σ (List.finRange ℓ)))]
  [HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q (Λ ∘ σ) ν)]
  [HasDerivedCategory.{w, 0} ℤ]

include hρ hQ in
/-- **Tor over `T` between standard-filtered modules with inequivalent labels** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, the off-diagonal `E²` terms): if `N` is
filtered by right standards `S_t` and `Y` by left standards, and no label of `N` is equivalent
to a label of `Y`, then `N ⊗ᴸ_T Y` has no cohomology. -/
theorem isZero_derivedTensorHomology_tensor_of_standardFiltrations
    (D : ModuleFiltration.OrderedStandardCovers
      (fun s : {s : Seq μ // IsRedOrdered s} => ModuleCat.of T (leftStandard Q (Λ ∘ σ) s.1 s.2))
      (fun s => seqIdem Q (Λ ∘ σ) s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    {m m' : List {s : Seq μ // IsRedOrdered s}} {N : ModuleCat.{0} Tᵐᵒᵖ} {Y : ModuleCat.{0} T}
    (hN : ModuleFiltration.HasFiltration
      (fun t : {s : Seq μ // IsRedOrdered s} =>
        tensorRightStandard (Λ := Λ) (ν := ν) hρ hQ σ t.1) m N)
    (hY : ModuleFiltration.HasFiltration (fun s : {s : Seq μ // IsRedOrdered s} =>
      ModuleCat.of T (leftStandard Q (Λ ∘ σ) s.1 s.2)) m' Y)
    (hlab : ∀ t ∈ m, ∀ s ∈ m', ¬ (StendhalLE s.1 t.1 ∧ StendhalLE t.1 s.1)) (n : ℤ) :
    IsZero ((homologyFunctor (A := ℤ) ℤ n).obj ((derivedTensor.{w} ℤ T N).obj
      (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor T).obj Y)))) := by
  have hN' := corner_filtration_right hρ hQ σ hN
  have hY' := corner_filtration_left hρ hQ σ hY
  exact isZero_derivedTensorHomology_of_ringEquiv (φ).symm N Y n
    (isZero_derivedTensorHomology_of_loadingFiltrations hρ hQ σ D hN' hY' hlab n)

include hρ hQ in
/-- **Higher Tor over `T` between standard-filtered modules vanish** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, the diagonal `E²` term). -/
theorem isZero_derivedTensorHomology_tensor_of_standardFiltrations_of_ne_zero
    (D : ModuleFiltration.OrderedStandardCovers
      (fun s : {s : Seq μ // IsRedOrdered s} => ModuleCat.of T (leftStandard Q (Λ ∘ σ) s.1 s.2))
      (fun s => seqIdem Q (Λ ∘ σ) s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    {m m' : List {s : Seq μ // IsRedOrdered s}} {N : ModuleCat.{0} Tᵐᵒᵖ} {Y : ModuleCat.{0} T}
    (hN : ModuleFiltration.HasFiltration
      (fun t : {s : Seq μ // IsRedOrdered s} =>
        tensorRightStandard (Λ := Λ) (ν := ν) hρ hQ σ t.1) m N)
    (hY : ModuleFiltration.HasFiltration (fun s : {s : Seq μ // IsRedOrdered s} =>
      ModuleCat.of T (leftStandard Q (Λ ∘ σ) s.1 s.2)) m' Y) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor (A := ℤ) ℤ n).obj ((derivedTensor.{w} ℤ T N).obj
      (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor T).obj Y)))) := by
  have hN' := corner_filtration_right hρ hQ σ hN
  have hY' := corner_filtration_left hρ hQ σ hY
  exact isZero_derivedTensorHomology_of_ringEquiv (φ).symm N Y n
    (isZero_derivedTensorHomology_of_loadingFiltrations_of_ne_zero hρ hQ σ D hN' hY' n hn)

end Categorification.Stendhal.BraidedStendhalAlgebra
