/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorRingEquiv
import Categorification.WeightedKLR.RedStrands.BraidedStandardTor

/-!
# Braiding functors on standardly filtered modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1,
proof of Lemma 6.11, step `f_n → s_n`: if the braid bimodule `B(κ', κ)` has a filtration by
right standards, then the braiding functor `- ⊗ᴸ B(κ, κ')` sends every module with a filtration
by right standards to a complex with homology only in degree `0`.

Through the corner flip, `- ⊗ᴸ B(κ, κ')` becomes a derived tensor over the corner itself,
whose coefficient is `B(κ', κ)` with its right action and whose module is the reflection of
the given one. Both carry filtrations by standards and reflected standards, and each pair of
layers has Tor concentrated in degree `0` (`isZero_derivedTensorHomology_loadingStandard`).

## Main results

* `isZero_braidingFunctor_homology_of_standardFiltration`: step `s_n`.
* `isZero_derivedTensorHomology_braidingBimodule`: the `Tor` part of step `p_{n+1}`.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory CategoryTheory.Limits KLR Equiv MulOpposite CornerEndomorphism
  ModuleFiltration DG DG.DerivedCategory

open scoped DG.DegreeZero

universe w
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q)

set_option quotPrecheck false in
local notation "C" κ:arg => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ
set_option quotPrecheck false in
local notation "B" κ':arg κ:arg => ↥(braidingBimodule k Q Λ ν κ' κ)
local notation "μ" => stendhalWeight ℓ ν

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

/-- The coefficient `B(κ, κ')` of `- ⊗ᴸ B(κ, κ')`, transported along the corner flip at `κ`, is
`B(κ', κ)` with its right action. -/
def braidingCoefficientFlipEquiv (κ κ' : List (Fin ℓ)) :
    ringEquivCoefficient (cornerFlipEquiv (Q := Q) (Λ := Λ) ν κ)
        (OpBimodule (C κ) (B κ κ')) ≃ₗ[(C κ)ᵐᵒᵖ] ModuleCat.of (C κ)ᵐᵒᵖ (B κ' κ) :=
  { braidingBimoduleFlip κ κ' with
    map_smul' := fun a x =>
      (braidingBimoduleFlip_smul_left κ κ' (cornerFlip a.unop) x).trans
        (by rw [cornerFlip_cornerFlip]; rfl) }

variable (σ : Perm (Fin ℓ))

local notation "κ" => List.map σ (List.finRange ℓ)

omit [DecidableEq I] in
/-- A non-violated loading of red order `σ ∘ (1, …, ℓ)` is the relabelling of a red-ordered
loading. -/
theorem exists_redPerm_of_redWord {s : Seq μ} (hs : redWord s = κ) :
    ∃ t : Seq μ, IsRedOrdered t ∧ Seq.redPerm σ t = s := by
  refine ⟨Seq.redPerm σ⁻¹ s, ?_, ?_⟩
  · rw [← redWord_eq_finRange_iff, redWord_redPerm, hs, List.map_map]
    simp
  · rw [Seq.redPerm_redPerm, mul_inv_cancel, Seq.redPerm_one]

include hρ hQ in
/-- **Braiding standardly filtered modules** (Webster, arXiv:1309.3796v2, proof of Lemma 6.11,
step `f_n → s_n`): if `B(κ', κ)` has a filtration by the right standards of the corner at
`κ = σ ∘ (1, …, ℓ)`, then `- ⊗ᴸ B(κ, κ')` sends every module with a filtration by these
standards to a complex with homology only in degree `0`. -/
theorem isZero_braidingFunctor_homology_of_standardFiltration
    [HasDerivedCategory.{w, 0} (C κ)] [HasDerivedCategory.{w, 0} ℤ]
    [HasDerivedCategory.{w, 0} (C κ)ᵐᵒᵖ] {κ' : List (Fin ℓ)}
    [HasDerivedCategory.{w, 0} (C κ')ᵐᵒᵖ]
    (D : ModuleFiltration.OrderedStandardCovers
      (fun s : {s : Seq μ // IsRedOrdered s} => ModuleCat.of (TensorProductAlgebra k Q (Λ ∘ σ) ν)
        (leftStandard Q (Λ ∘ σ) s.1 s.2))
      (fun s => seqIdem Q (Λ ∘ σ) s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    {m : List {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s}}
    (hf : HasFiltration
      (fun s => ModuleCat.of (C κ)ᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.val κ)) m
      (ModuleCat.of (C κ)ᵐᵒᵖ (B κ' κ)))
    {m' : List {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s}} {X : ModuleCat.{0} (C κ)ᵐᵒᵖ}
    (hX : HasFiltration
      (fun s => ModuleCat.of (C κ)ᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.val κ)) m'
      X)
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor (A := (C κ')ᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor.{w} k Q Λ ν κ κ').obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (C κ)ᵐᵒᵖ).obj X)))) := by
  let φ := cornerFlipEquiv (Q := Q) (Λ := Λ) ν κ
  refine isZero_derivedTensorHomology_of_ringEquiv φ (OpBimodule (C κ) (B κ κ')) X n ?_
  refine isZero_derivedTensorHomology_of_filtrations
    (hf.of_equiv (braidingCoefficientFlipEquiv κ κ').symm)
    (hX.restrictScalars φ.symm.toRingHom) n fun c _ d _ => ?_
  obtain ⟨t, ht, htc⟩ := exists_redPerm_of_redWord σ c.2.1
  obtain ⟨s, hs, hsd⟩ := exists_redPerm_of_redWord σ d.2.1
  have := isZero_derivedTensorHomology_loadingStandard hρ hQ σ D hs ht n hn
  rw [htc, hsd] at this
  exact this

include hρ hQ in
/-- **Composites of braid bimodules have no higher `Tor`** (Webster, arXiv:1309.3796v2, proof of
Lemma 6.11, step `s_n + f_n → p_{n+1}`): if `B(κ₂, κ₁)` and `B(κ₀, κ₁)` have filtrations by the
right standards of the corner at `κ₁ = σ ∘ (1, …, ℓ)`, then `B(κ₂, κ₁) ⊗ᴸ B(κ₁, κ₀)` has homology
only in degree `0`. Its degree-zero homology is the balanced tensor product, which is
`B(κ₂, κ₀)` when the lengths add (Lemma 6.5, `violMk_mult_injective`, `violMk_mult_surjective`). -/
theorem isZero_derivedTensorHomology_braidingBimodule
    [HasDerivedCategory.{w, 0} (C κ)] [HasDerivedCategory.{w, 0} ℤ]
    (D : ModuleFiltration.OrderedStandardCovers
      (fun s : {s : Seq μ // IsRedOrdered s} => ModuleCat.of (TensorProductAlgebra k Q (Λ ∘ σ) ν)
        (leftStandard Q (Λ ∘ σ) s.1 s.2))
      (fun s => seqIdem Q (Λ ∘ σ) s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    {κ₂ κ₀ : List (Fin ℓ)} {m m' : List {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s}}
    (h₂ : HasFiltration
      (fun s => ModuleCat.of (C κ)ᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.val κ)) m
      (ModuleCat.of (C κ)ᵐᵒᵖ (B κ₂ κ)))
    (h₀ : HasFiltration
      (fun s => ModuleCat.of (C κ)ᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.val κ)) m'
      (ModuleCat.of (C κ)ᵐᵒᵖ (B κ₀ κ)))
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor (A := ℤ) ℤ n).obj
      ((derivedTensor.{w} ℤ (C κ) (ModuleCat.of (C κ)ᵐᵒᵖ (B κ₂ κ))).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (C κ)).obj
          (ModuleCat.of (C κ) (B κ κ₀)))))) := by
  refine isZero_derivedTensorHomology_of_filtrations h₂
    (hasReflectedStandardFiltration_braidingBimodule κ κ₀ h₀) n fun c _ d _ => ?_
  obtain ⟨t, ht, htc⟩ := exists_redPerm_of_redWord σ c.2.1
  obtain ⟨s, hs, hsd⟩ := exists_redPerm_of_redWord σ d.2.1
  have := isZero_derivedTensorHomology_loadingStandard hρ hQ σ D hs ht n hn
  rw [htc, hsd] at this
  exact this

end Categorification.Stendhal.BraidedStendhalAlgebra
