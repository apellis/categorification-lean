/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedBraidFunctor
import Categorification.WeightedKLR.RedStrands.BraidedRelabelAppend
import Categorification.WeightedKLR.RedStrands.BraidedViolatedQuotient
import Categorification.Algebra.Graded.RectBimodTensor

set_option backward.isDefEq.respectTransparency false

/-!
# Composites of graded braid functors

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1,
Lemma 6.5 and the proof of Lemma 6.11.

For permutations `τ` and `σ` of the red strands such that every pair inverted by `τ` stays
inverted by `τ * σ` (the length-additive case), the graded braiding bimodule of `τ * σ` is the
balanced tensor product of the braiding bimodules of `σ` (relabelled along `τ`) and of `τ`.

## Main results

* `redPermAlgEquiv_redPermAlgEquiv`, `violRedPermEquiv_violRedPermEquiv`: relabelling the red
  strands along `σ` and then `τ` is relabelling along `τ * σ`.
* `braidBimodCompEquiv`: the graded tensor-product decomposition of the braiding bimodule of
  `τ * σ` (Lemma 6.5 in the graded setting).
* `braidFunctorCompIso`: the corresponding isomorphism of graded braid functors
  `B_σ ∘ B_τ ≅ B_{τσ}` on finite-dimensional graded modules.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR TypeA Equiv Categorification.Graded MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

section RedPerm

variable {Λ Λ' Λ'' : Fin ℓ → I →₀ ℕ} (τ σ : Perm (Fin ℓ)) (h₁ : ∀ r, Λ' r = Λ (τ r))
  (h₂ : ∀ r, Λ'' r = Λ' (σ r))

/-- Relabelling along `σ` and then along `τ` is relabelling along `τ σ`. -/
theorem redPermAlgEquiv_redPermAlgEquiv (x : BraidedStendhalAlgebra k Q Λ'' ν) :
    redPermAlgEquiv τ h₁ (redPermAlgEquiv σ h₂ x) =
      redPermAlgEquiv (τ * σ) (fun r => (h₂ r).trans (h₁ (σ r))) x := by
  obtain ⟨u, rfl⟩ := ofKLR_surjective x
  have h : ((redPermAlgEquiv τ h₁).toAlgHom.comp ((redPermAlgEquiv σ h₂).toAlgHom.comp
      (ofKLR k Q Λ'' ν))) =
      (redPermAlgEquiv (τ * σ) (fun r => (h₂ r).trans (h₁ (σ r)))).toAlgHom.comp
        (ofKLR k Q Λ'' ν) := by
    apply RingQuot.ringQuot_ext'
    apply FreeAlgebra.hom_ext
    funext g
    cases g with
    | idem i =>
      change redPermAlgEquiv τ h₁ (redPermAlgEquiv σ h₂ (ofKLR k Q Λ'' ν (KLRAlgebra.e i))) =
        redPermAlgEquiv (τ * σ) _ (ofKLR k Q Λ'' ν (KLRAlgebra.e i))
      rw [redPermAlgEquiv_e, redPermAlgEquiv_e, redPermAlgEquiv_e, Seq.redPerm_redPerm]
    | dot a =>
      change redPermAlgEquiv τ h₁ (redPermAlgEquiv σ h₂ (ofKLR k Q Λ'' ν (KLRAlgebra.x a))) =
        redPermAlgEquiv (τ * σ) _ (ofKLR k Q Λ'' ν (KLRAlgebra.x a))
      rw [redPermAlgEquiv_x, redPermAlgEquiv_x, redPermAlgEquiv_x]
    | cross j =>
      change redPermAlgEquiv τ h₁ (redPermAlgEquiv σ h₂ (ofKLR k Q Λ'' ν (KLRAlgebra.ψ j))) =
        redPermAlgEquiv (τ * σ) _ (ofKLR k Q Λ'' ν (KLRAlgebra.ψ j))
      rw [redPermAlgEquiv_ψ, redPermAlgEquiv_ψ, redPermAlgEquiv_ψ]
  exact DFunLike.congr_fun h u

/-- Relabelling along `σ` and then along `τ` is relabelling along `τ σ`, on the quotient by
violated idempotents. -/
theorem violRedPermEquiv_violRedPermEquiv (x : ViolQuotient k Q Λ'' ν) :
    violRedPermEquiv τ h₁ (violRedPermEquiv σ h₂ x) =
      violRedPermEquiv (τ * σ) (fun r => (h₂ r).trans (h₁ (σ r))) x := by
  obtain ⟨y, rfl⟩ := violMk_surjective x
  rw [violRedPermEquiv_violMk, violRedPermEquiv_violMk, violRedPermEquiv_violMk,
    redPermAlgEquiv_redPermAlgEquiv]

end RedPerm

section Compose

variable {Λ : Fin ℓ → I →₀ ℕ} {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : IsReducedChoice ρ) (hQ : KLRSymm Q) (τ σ : Perm (Fin ℓ))

local notation "φ" => violRedPermEquiv (k := k) (Q := Q) (Λ' := Λ ∘ τ) (Λ := Λ) (ν := ν) τ
  (fun _ => rfl)

/-- Relabelling along `τ` carries the corner map of `σ` for `λ ∘ τ` to that of `τ σ`. -/
theorem violRedPermEquiv_permCornerMap (u : TensorProductAlgebra k Q ((Λ ∘ τ) ∘ σ) ν) :
    φ (permCornerMap Q (Λ ∘ τ) ν hρ hQ σ u) = permCornerMap Q Λ ν hρ hQ (τ * σ) u := by
  rw [permCornerMap_apply, permCornerMap_apply, violRedPermEquiv_violRedPermEquiv]
  rfl

theorem perm_map_finRange (σ' τ' : Perm (Fin ℓ)) :
    ((List.finRange ℓ).map σ').Perm ((List.finRange ℓ).map τ') := by
  rw [List.perm_ext_iff_of_nodup ((List.nodup_finRange ℓ).map σ'.injective)
    ((List.nodup_finRange ℓ).map τ'.injective)]
  intro a
  simp only [List.mem_map, List.mem_finRange, true_and]
  exact ⟨fun _ => ⟨τ'.symm a, τ'.apply_symm_apply a⟩, fun _ => ⟨σ'.symm a, σ'.apply_symm_apply a⟩⟩

omit [DecidableEq I] in
theorem nodup_map_finRange (σ' : Perm (Fin ℓ)) : ((List.finRange ℓ).map σ').Nodup :=
  (List.nodup_finRange ℓ).map σ'.injective

theorem CornerTensor.mult_injective_congr {A : Type*} [Ring A] [Algebra k A]
    {e₂ e₁ e₀ f₂ f₁ f₀ : A} (h₂ : IsIdempotentElem e₂) (h₁ : IsIdempotentElem e₁)
    (h₀ : IsIdempotentElem e₀) (g₂ : IsIdempotentElem f₂) (g₁ : IsIdempotentElem f₁)
    (g₀ : IsIdempotentElem f₀) (he₂ : e₂ = f₂) (he₁ : e₁ = f₁) (he₀ : e₀ = f₀)
    (h : Function.Injective (CornerTensor.mult (k := k) g₂ g₁ g₀)) :
    Function.Injective (CornerTensor.mult (k := k) h₂ h₁ h₀) := by
  subst he₂ he₁ he₀
  exact h

theorem CornerTensor.mult_surjective_congr {A : Type*} [Ring A] [Algebra k A]
    {e₂ e₁ e₀ f₂ f₁ f₀ : A} (h₂ : IsIdempotentElem e₂) (h₁ : IsIdempotentElem e₁)
    (h₀ : IsIdempotentElem e₀) (g₂ : IsIdempotentElem f₂) (g₁ : IsIdempotentElem f₁)
    (g₀ : IsIdempotentElem f₀) (he₂ : e₂ = f₂) (he₁ : e₁ = f₁) (he₀ : e₀ = f₀)
    (h : ∀ y, ∃ t, CornerTensor.mult (k := k) g₂ g₁ g₀ t = f₂ * y * f₀) :
    ∀ y, ∃ t, CornerTensor.mult (k := k) h₂ h₁ h₀ t = e₂ * y * e₀ := by
  subst he₂ he₁ he₀
  exact h

variable (H : ∀ x y, List.Sublist [x, y] ((List.finRange ℓ).map ⇑(τ * σ)) →
  List.Sublist [y, x] ((List.finRange ℓ).map τ) → List.Sublist [y, x] (List.finRange ℓ))

local notation "α₀" => identityCornerMap Q Λ ν hρ hQ
local notation "β₀" => permCornerMap Q Λ ν hρ hQ τ
local notation "γ₀" => (permCornerMap Q Λ ν hρ hQ (τ * σ) :
  TensorProductAlgebra k Q ((Λ ∘ τ) ∘ σ) ν →ₙₐ[k] ViolQuotient k Q Λ ν)
local notation "β₀'" => identityCornerMap Q (Λ ∘ τ) ν hρ hQ
local notation "γ₀'" => permCornerMap Q (Λ ∘ τ) ν hρ hQ σ

include H in
/-- **Webster, Lemma 6.5, for the braiding bimodules**: when the lengths add,
`B_τ ⊗_{T^{λ ∘ τ}} B_σ ≅ B_{τ σ}` as graded bimodules, by multiplication after relabelling
`B_σ` (for the labels `λ ∘ τ`) along `τ`. -/
def braidBimodCompEquiv :
    BalancedTensor k (TensorProductAlgebra k Q ((Λ ∘ τ) ∘ σ) ν)ᵐᵒᵖ
      (TensorProductAlgebra k Q (Λ ∘ τ) ν)ᵐᵒᵖ (braidBimod Q (Λ ∘ τ) ν hρ hQ σ)
      (braidBimod Q Λ ν hρ hQ τ) ≃ₗ[(TensorProductAlgebra k Q ((Λ ∘ τ) ∘ σ) ν)ᵐᵒᵖ]
      RectBimod α₀ γ₀ :=
  RectBimod.tensorMulEquiv φ (α := α₀) (β := β₀) (γ := γ₀) (β' := β₀') (γ' := γ₀')
    (fun _ => rfl) (violRedPermEquiv_permCornerMap hρ hQ τ σ)
    (fun c hc => exists_permCornerMap_eq hρ hQ τ (by rwa [permCornerMap_one] at hc))
    (CornerTensor.mult_injective_congr _ _ _ _ _ _ (identityCornerMap_one hρ hQ)
      (permCornerMap_one hρ hQ τ) (permCornerMap_one hρ hQ (τ * σ))
      (violMk_mult_injective hρ hQ (nodup_map_finRange _) (perm_map_finRange _ _) H))
    (CornerTensor.mult_surjective_congr _ _ _ _ _ _ (identityCornerMap_one hρ hQ)
      (permCornerMap_one hρ hQ τ) (permCornerMap_one hρ hQ (τ * σ))
      (violMk_mult_surjective hρ hQ (nodup_map_finRange _) (perm_map_finRange _ _) H))

theorem braidBimodCompEquiv_apply (y : braidBimod Q (Λ ∘ τ) ν hρ hQ σ)
    (x : braidBimod Q Λ ν hρ hQ τ) :
    RectBimod.val α₀ γ₀ (braidBimodCompEquiv (Λ := Λ) hρ hQ τ σ H (BalancedTensor.tmul y x)) =
      RectBimod.val α₀ β₀ x * φ (RectBimod.val β₀' γ₀' y) := rfl

theorem isBimoduleHom_braidBimodCompEquiv :
    BalancedTensor.IsBimoduleHom (A := (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ)
      (braidBimodCompEquiv (Λ := Λ) hρ hQ τ σ H).toLinearMap :=
  RectBimod.isBimoduleHom_tensorMul φ (fun _ => rfl) (violRedPermEquiv_permCornerMap hρ hQ τ σ)

variable {𝔠 : QuantumGroup.CartanDatum I} (hR : IsRouquierQ 𝔠 Q)

theorem braidBimodCompEquiv_mem {d : ℤ} {t : BalancedTensor k
      (TensorProductAlgebra k Q ((Λ ∘ τ) ∘ σ) ν)ᵐᵒᵖ (TensorProductAlgebra k Q (Λ ∘ τ) ν)ᵐᵒᵖ
      (braidBimod Q (Λ ∘ τ) ν hρ hQ σ) (braidBimod Q Λ ν hρ hQ τ)}
    (ht : t ∈ balancedGrading (TensorProductAlgebra k Q ((Λ ∘ τ) ∘ σ) ν)ᵐᵒᵖ
      (TensorProductAlgebra k Q (Λ ∘ τ) ν)ᵐᵒᵖ (braidBimodGrading Q (Λ ∘ τ) ν hρ hQ σ hR)
      (braidBimodGrading Q Λ ν hρ hQ τ hR) d) :
    braidBimodCompEquiv (Λ := Λ) hρ hQ τ σ H t ∈
      RectBimod.grading (violAuxiliaryGrade (ν := ν) (rouquierGrading Q hR Λ)) α₀ γ₀ d :=
  RectBimod.tensorMul_mem_grading φ (fun _ => rfl) (violRedPermEquiv_permCornerMap hρ hQ τ σ)
    _ _ (fun _ y hy => (violRedPermEquiv_mem_grade_iff hR τ y).2 hy) ht

variable [∀ (Ω : Fin ℓ → I →₀ ℕ), Module.Finite k (TensorProductAlgebra k Q Ω ν)]

local notation "𝒜" Ω => oppositeGrade (tensorProductGrade (rouquierGrading Q hR Ω) ν)
local notation "T" Ω => TensorProductAlgebra k Q Ω ν

/-- **Composites of braid functors** (Webster, arXiv:1309.3796v2, Lemma 6.5, on modules): when
the lengths add, `𝔅_σ (𝔅_τ N) ≅ 𝔅_{τ σ} N` as graded modules, where `𝔅_σ` is the braid functor
for the labels `λ ∘ τ`. -/
def braidFunctorCompIso (N : GFin (𝒜 Λ)) :
    (braidFunctor (Λ := Λ ∘ τ) hρ hQ σ hR (braidFunctor (Λ := Λ) hρ hQ τ hR N)).Iso
      (braidFunctor (Λ := Λ) hρ hQ (τ * σ) hR N) :=
  letI := braidBimodDecomposition (Λ := Λ) (ν := ν) hρ hQ τ hR
  letI := braidBimod_gradedSMul_left (Λ := Λ) (ν := ν) hρ hQ τ hR
  letI := braidBimod_gradedSMul_right (Λ := Λ) (ν := ν) hρ hQ τ hR
  letI := finite_braidBimod (Λ := Λ) (ν := ν) hρ hQ τ
  letI := braidBimodDecomposition (Λ := Λ ∘ τ) (ν := ν) hρ hQ σ hR
  letI := braidBimod_gradedSMul_left (Λ := Λ ∘ τ) (ν := ν) hρ hQ σ hR
  letI := braidBimod_gradedSMul_right (Λ := Λ ∘ τ) (ν := ν) hρ hQ σ hR
  letI := finite_braidBimod (Λ := Λ ∘ τ) (ν := ν) hρ hQ σ
  letI : DirectSum.Decomposition (RectBimod.grading (violAuxiliaryGrade (ν := ν)
      (rouquierGrading Q hR Λ)) α₀ γ₀) := braidBimodDecomposition (Λ := Λ) (ν := ν) hρ hQ (τ * σ) hR
  letI : SetLike.GradedSMul (oppositeGrade (oppositeGrade (tensorProductGrade
      (rouquierGrading Q hR Λ) ν))) (RectBimod.grading (violAuxiliaryGrade (ν := ν)
      (rouquierGrading Q hR Λ)) α₀ γ₀) :=
    braidBimod_gradedSMul_left (Λ := Λ) (ν := ν) hρ hQ (τ * σ) hR
  letI : SetLike.GradedSMul (𝒜 ((Λ ∘ τ) ∘ σ)) (RectBimod.grading (violAuxiliaryGrade (ν := ν)
      (rouquierGrading Q hR Λ)) α₀ γ₀) :=
    braidBimod_gradedSMul_right (Λ := Λ) (ν := ν) hρ hQ (τ * σ) hR
  letI : Module.Finite k (RectBimod α₀ γ₀) := finite_braidBimod (Λ := Λ) (ν := ν) hρ hQ (τ * σ)
  letI := compDecomposition (C := (T ((Λ ∘ τ) ∘ σ))ᵐᵒᵖ) (𝒜 (Λ ∘ τ))
    (braidBimodGrading Q Λ ν hρ hQ τ hR) (braidBimodGrading Q (Λ ∘ τ) ν hρ hQ σ hR)
  letI := compGradedSMul (B := (T (Λ ∘ τ))ᵐᵒᵖ) (𝒜 ((Λ ∘ τ) ∘ σ))
    (braidBimodGrading Q Λ ν hρ hQ τ hR) (braidBimodGrading Q (Λ ∘ τ) ν hρ hQ σ hR)
  letI := compGradedSMulRight (B := (T (Λ ∘ τ))ᵐᵒᵖ) (C := (T ((Λ ∘ τ) ∘ σ))ᵐᵒᵖ) (𝒜 Λ)
    (braidBimodGrading Q Λ ν hρ hQ τ hR) (braidBimodGrading Q (Λ ∘ τ) ν hρ hQ σ hR)
  letI := finite_balancedTensor (k := k) (B := (T ((Λ ∘ τ) ∘ σ))ᵐᵒᵖ) (A := (T (Λ ∘ τ))ᵐᵒᵖ)
    (M := braidBimod Q (Λ ∘ τ) ν hρ hQ σ) (braidBimod Q Λ ν hρ hQ τ)
  (GFin.induceInduceIso (𝒜 Λ) (𝒜 (Λ ∘ τ)) (𝒜 ((Λ ∘ τ) ∘ σ))
    (braidBimodGrading Q Λ ν hρ hQ τ hR) (braidBimodGrading Q (Λ ∘ τ) ν hρ hQ σ hR) N).trans
    (GFin.induceCongrLeft (braidBimodCompEquiv (Λ := Λ) hρ hQ τ σ H)
      (isBimoduleHom_braidBimodCompEquiv hρ hQ τ σ H)
      (fun _ _ hm => braidBimodCompEquiv_mem hρ hQ τ σ H hR hm) N)

end Compose

end Categorification.Stendhal.BraidedStendhalAlgebra
