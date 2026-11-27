/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidRightSequenceCut
import Categorification.WeightedKLR.RedStrands.BraidingFunctorComp
import Categorification.Algebra.DerivedTensorProjective

set_option backward.isDefEq.respectTransparency false

/-!
# The higher `Tor` of composable braiding bimodules vanish

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Lemma 6.12. Let `τ` and `s` be permutations of the red strands, with red orders
`κ₂ = (1, …, ℓ)`, `κ₁ = τ(1, …, ℓ)` and `κ₀ = τs(1, …, ℓ)`. If the braid functors `𝔅_τ` (for
the labels `λ`) and `𝔅_{s⁻¹}` (for the labels `λ ∘ τ ∘ s`) send sequence projectives to modules
with standard filtrations, then the braiding bimodules `B(κ₂, κ₁)` and `B(κ₀, κ₁)` have
filtrations by the right standards of the corner at `κ₁`, and so the derived braiding of
`B(κ₂, κ₁)` along `B(κ₁, κ₀)` has homology only in degree `0`
(`isZero_braidingFunctor_braidingBimodule_homology`). This is the `Tor` hypothesis of
`braidingFunctorCompIso`. At `τ = 1` it holds because `B(κ₁, κ₁)` is projective
(`isZero_braidingFunctor_braidingBimodule_self_homology`).

## Main results

* `exists_hasFiltration_violCorner_of_braidFunctor_inv`: the cut `e(u) V e_λ` of red order
  `σ(1, …, ℓ)` is filtered by the right standards of the identity red order.
* `isZero_braidingFunctor_braidingBimodule_homology`,
  `isZero_braidingFunctor_braidingBimodule_self_homology`.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory CategoryTheory.Limits KLR TypeA Equiv Categorification.Graded MulOpposite
  ModuleFiltration DG DG.DerivedCategory

open scoped DG.DegreeZero List

universe w

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : IsReducedChoice ρ) (hQ : KLRSymm Q)
  {𝔠 : QuantumGroup.CartanDatum I} (hR : IsRouquierQ 𝔠 Q)
  [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I), Module.Finite k (TensorProductAlgebra k Q Ω ν)]

local notation "ord" => List.finRange ℓ
local notation "μ" => stendhalWeight ℓ ν

include hρ hQ in
/-- **Cuts of the braiding bimodule of `σ`** (Webster, arXiv:1309.3796v2, proof of Lemma 6.11):
if `𝔅_{σ⁻¹}` sends every sequence projective of `T^{λ ∘ σ}` to a module with a standard
filtration, every cut `e(u) V e_λ` with `u` of red order `σ(1, …, ℓ)` has a filtration by the
loading standards of the identity red order. -/
theorem exists_hasFiltration_violCorner_of_braidFunctor_inv (Λ : Fin ℓ → I →₀ ℕ)
    (σ : Perm (Fin ℓ))
    (h : ∀ (t : Seq μ) (ht : IsRedOrdered t), HasCornerStandardFiltration ((Λ ∘ σ) ∘ ⇑σ⁻¹) ν
      hρ hQ hR (braidFunctor (Λ := Λ ∘ σ) (ν := ν) hρ hQ σ⁻¹ hR
        (rightSequenceProj (rouquierGrading Q hR (Λ ∘ σ)) t ht).toGFin))
    (u : Seq μ) (hu : redWord u = (List.finRange ℓ).map σ) :
    ∃ m : List {s : Seq μ // redWord s = ord ∧ ¬ IsViolated s},
      HasFiltration (fun s => ModuleCat.of (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
          ord)ᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.1 ord)) m
        (ModuleCat.of (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) ord)ᵐᵒᵖ
          (violCorner k Q Λ ν u ord)) := by
  have hord : IsRedOrdered (Seq.redPerm σ⁻¹ u) := by
    rw [← redWord_eq_finRange_iff, redWord_redPerm, hu, List.map_map]
    simp
  have h2 := exists_hasFiltration_violCorner_relabel (k := k) (Q := Q) (Λ := Λ) (ν := ν) σ
    (exists_hasFiltration_violCorner_of_braidFunctor (Λ := Λ ∘ σ) hρ hQ hR σ⁻¹ _ hord (h _ hord))
  rw [Seq.redPerm_redPerm, mul_inv_cancel, Seq.redPerm_one] at h2
  have hκ : ((List.finRange ℓ).map ⇑σ⁻¹).map ⇑σ = ord := by simp [List.map_map]
  generalize ((List.finRange ℓ).map ⇑σ⁻¹).map ⇑σ = κ at hκ h2
  subst hκ
  exact h2

variable [HasDerivedCategory.{w, 0} ℤ]

include hρ hQ in
/-- **The higher `Tor` of composable braiding bimodules vanish** (Webster, arXiv:1309.3796v3,
proof of Lemma 6.12): for the red orders `κ₂ = (1, …, ℓ)`, `κ₁ = τ κ₂` and `κ₀ = τ s κ₂`, if
`𝔅_τ` (labels `λ`) and `𝔅_{s⁻¹}` (labels `λ ∘ τ ∘ s`) send sequence projectives to modules with
standard filtrations, then `B(κ₂, κ₁) ⊗ᴸ B(κ₁, κ₀)` has homology only in degree `0`. Route
hypothesis: `AllFiniteDeltaInjective` (Corollary 5.21). -/
theorem isZero_braidingFunctor_braidingBimodule_homology (Λ : Fin ℓ → I →₀ ℕ)
    (τ s : Perm (Fin ℓ))
    [HasDerivedCategory.{w, 0} (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
      ((List.finRange ℓ).map τ))]
    [HasDerivedCategory.{w, 0} (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
      ((List.finRange ℓ).map τ))ᵐᵒᵖ]
    [HasDerivedCategory.{w, 0} (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
      ((List.finRange ℓ).map ⇑(τ * s)))ᵐᵒᵖ]
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)
    (hτ : ∀ (t : Seq μ) (ht : IsRedOrdered t), HasCornerStandardFiltration (Λ ∘ τ) ν
      hρ hQ hR (braidFunctor (Λ := Λ) (ν := ν) hρ hQ τ hR
        (rightSequenceProj (rouquierGrading Q hR Λ) t ht).toGFin))
    (hs : ∀ (t : Seq μ) (ht : IsRedOrdered t), HasCornerStandardFiltration
      (((Λ ∘ τ) ∘ s) ∘ ⇑s⁻¹) ν hρ hQ hR (braidFunctor (Λ := (Λ ∘ τ) ∘ s) (ν := ν) hρ hQ s⁻¹ hR
        (rightSequenceProj (rouquierGrading Q hR ((Λ ∘ τ) ∘ s)) t ht).toGFin))
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor (A := (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
        ((List.finRange ℓ).map ⇑(τ * s)))ᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor.{w} k Q Λ ν ((List.finRange ℓ).map τ) ((List.finRange ℓ).map ⇑(τ * s))).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (ViolOrderCorner (k := k) (Q := Q)
          (Λ := Λ) (ν := ν) ((List.finRange ℓ).map τ))ᵐᵒᵖ).obj
          (ModuleCat.of (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
            ((List.finRange ℓ).map τ))ᵐᵒᵖ
            (braidingBimodule k Q Λ ν (List.finRange ℓ) ((List.finRange ℓ).map τ))))))) := by
  -- `B(κ₂, κ₁)` is filtered by the standards of the corner at `κ₁`
  obtain ⟨m', hX⟩ := exists_hasFiltration_braidingBimodule (k := k) (Q := Q) (Λ := Λ) (ν := ν)
    (List.finRange ℓ) ((List.finRange ℓ).map τ) fun t ht =>
      exists_hasFiltration_violCorner_of_braidFunctor hρ hQ hR τ t
        ((redWord_eq_finRange_iff t).1 ht) (hτ t ((redWord_eq_finRange_iff t).1 ht))
  -- `B(κ₀, κ₁)` is the relabelling of `B(s, 1)` for the labels `λ ∘ τ`
  obtain ⟨m, hf⟩ := exists_hasFiltration_braidingBimodule (k := k) (Q := Q) (Λ := Λ) (ν := ν)
    ((List.finRange ℓ).map ⇑(τ * s)) ((List.finRange ℓ).map τ) fun u hu => by
      have hu' : redWord (Seq.redPerm τ⁻¹ u) = (List.finRange ℓ).map s := by
        rw [redWord_redPerm, hu, List.map_map]
        ext1
        simp [Function.comp_def]
      have h2 := exists_hasFiltration_violCorner_relabel (k := k) (Q := Q) (Λ := Λ) (ν := ν) τ
        (exists_hasFiltration_violCorner_of_braidFunctor_inv hρ hQ hR (Λ ∘ τ) s hs _ hu')
      rwa [Seq.redPerm_redPerm, mul_inv_cancel, Seq.redPerm_one] at h2
  let D := orderedStandardCovers Q (Λ ∘ τ)
    (fun s => exists_hasFiltration_leftUpper Q hQ hR hall (Λ ∘ τ) ν s.1 s.2)
  exact isZero_braidingFunctor_homology_of_standardFiltration hρ hQ τ D hf hX n hn


omit [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I), Module.Finite k (TensorProductAlgebra k Q Ω ν)]
  [HasDerivedCategory.{w, 0} ℤ] in
/-- **The `Tor` hypothesis at the identity** (Webster, arXiv:1309.3796v3, Lemma 6.12 with
`w s_i = 1`): `B(κ₁, κ₁)` is the corner at `κ₁`, a projective right module, so its derived
braiding has homology only in degree `0`. -/
theorem isZero_braidingFunctor_braidingBimodule_self_homology {Λ : Fin ℓ → I →₀ ℕ}
    {κ₂ κ₁ κ₀ : List (Fin ℓ)} (h : κ₂ = κ₁)
    [HasDerivedCategory.{w, 0} (isIdempotentElem_violMk_redProj k Q Λ ν κ₁).Cornerᵐᵒᵖ]
    [HasDerivedCategory.{w, 0} (isIdempotentElem_violMk_redProj k Q Λ ν κ₀).Cornerᵐᵒᵖ]
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor (A := (isIdempotentElem_violMk_redProj k Q Λ ν κ₀).Cornerᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor.{w} k Q Λ ν κ₁ κ₀).obj
        (DG.DerivedCategory.Q.obj (DGModuleCat.of (isIdempotentElem_violMk_redProj k Q Λ ν κ₁).Cornerᵐᵒᵖ
          (cornerOpDZ (isIdempotentElem_violMk_redProj k Q Λ ν κ₂)
            (violMk k Q Λ ν (redProj k Q Λ ν κ₁))))))) := by
  subst h
  have : Module.Projective (isIdempotentElem_violMk_redProj k Q Λ ν κ₂).Cornerᵐᵒᵖ
      (OpBimodule (isIdempotentElem_violMk_redProj k Q Λ ν κ₂).Corner
        (cornerBimodule (violMk k Q Λ ν (redProj k Q Λ ν κ₂))
          (violMk k Q Λ ν (redProj k Q Λ ν κ₂)))) :=
    projective_cornerBimodule_self (isIdempotentElem_violMk_redProj k Q Λ ν κ₂)
  exact isZero_derivedTensor_homology_of_projective _ _ n hn

end Categorification.Stendhal.BraidedStendhalAlgebra
