/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongQuotient
import Categorification.Algebra.InductionAlongQuotientModule

/-!
# Induction of a quotient module, modulo a kernel

For a nonunital ring map `φ : A → B`, a ring map `π_B : B → B'`, an `A`-module `N` and a
submodule `N'`, the quotient of `Ind_φ (N / N')` by `ker(π_B) · Ind_φ (N / N')` is the quotient of
`Ind_φ N` by the span of `indImageSub φ N'` and `ker(π_B) · Ind_φ N`
(`InductionAlong.indQuotSupEquiv`). Induction along a linear isomorphism is a linear isomorphism
(`InductionAlong.indMapLinEquiv`), and it carries `ker(π_B) · Ind_φ N` onto its counterpart
(`InductionAlong.map_indKerSub`).

## Main definitions

* `InductionAlong.indMapLinEquiv`: `Ind_φ N ≅ Ind_φ N'` for `N ≅ N'`.
* `InductionAlong.indQuotSupEquiv`:
  `Ind_φ (N / N') / ker(π_B) · Ind_φ (N / N') ≅ Ind_φ N / (indImageSub φ N' ⊔ ker(π_B) · Ind_φ N)`.
-/

namespace Categorification

open MulOpposite

noncomputable section

namespace InductionAlong

universe u w

section Span

variable {B B' : Type*} [Ring B] [Ring B'] (πB : B →+* B')
  {M M' : Type*} [AddCommGroup M] [Module B M] [AddCommGroup M'] [Module B M']

/-- A surjective linear map carries `ker(π_B) · M` onto `ker(π_B) · M'`. -/
theorem map_span_kerSmul {f : M →ₗ[B] M'} (hf : Function.Surjective f) :
    (Submodule.span B {x : M | ∃ b : B, πB b = 0 ∧ ∃ y : M, x = b • y}).map f =
      Submodule.span B {x : M' | ∃ b : B, πB b = 0 ∧ ∃ y : M', x = b • y} := by
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨b, hb, y, rfl⟩, rfl⟩
    exact ⟨b, hb, f y, map_smul f b y⟩
  · rintro ⟨b, hb, y, rfl⟩
    obtain ⟨y, rfl⟩ := hf y
    exact ⟨b • y, ⟨b, hb, y, rfl⟩, map_smul f b y⟩

end Span

variable {A B B' : Type u} [Ring A] [Ring B] [Ring B'] {φ : A →ₙ+* B} (πB : B →+* B')
  {N N' : Type w} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']

/-- Induction preserves surjectivity. -/
theorem indMap_surjective {g : N →ₗ[A] N'} (hg : Function.Surjective g) :
    Function.Surjective (Ind.map (φ := φ) g) := by
  intro x
  induction x using Ind.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul z n =>
    obtain ⟨n, rfl⟩ := hg n
    exact ⟨Ind.tmul z n, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ a b⟩

variable (φ) in
/-- **Induction along a linear isomorphism.** -/
def indMapLinEquiv (e : N ≃ₗ[A] N') : Ind N φ ≃ₗ[B] Ind N' φ :=
  LinearEquiv.ofLinearMap (Ind.map e.toLinearMap) (Ind.map e.symm.toLinearMap)
    (Ind.ext fun z n => by
      rw [LinearMap.comp_apply, Ind.map_tmul, Ind.map_tmul, LinearEquiv.coe_coe,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rfl)
    (Ind.ext fun z n => by
      rw [LinearMap.comp_apply, Ind.map_tmul, Ind.map_tmul, LinearEquiv.coe_coe,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      rfl)

theorem indMapLinEquiv_tmul (e : N ≃ₗ[A] N') (z : Corner φ) (n : N) :
    indMapLinEquiv φ e (Ind.tmul z n) = Ind.tmul z (e n) := rfl

/-- Induction along a surjection carries `ker(π_B) · Ind_φ N` onto `ker(π_B) · Ind_φ N'`. -/
theorem map_indKerSub {g : N →ₗ[A] N'} (hg : Function.Surjective g) :
    (indKerSub φ πB N).map (Ind.map g) = indKerSub φ πB N' :=
  map_span_kerSmul πB (indMap_surjective hg)

variable (φ) {N₀ : Type w} [AddCommGroup N₀] [Module A N₀] (S : Submodule A N₀)

theorem map_indModQuotEquiv_symm_indKerSub :
    (indKerSub φ πB (N₀ ⧸ S)).map (indModQuotEquiv φ S).symm.toLinearMap =
      (indKerSub φ πB N₀).map (indImageSub φ S).mkQ := by
  rw [indKerSub, indKerSub, map_span_kerSmul πB (indModQuotEquiv φ S).symm.surjective,
    map_span_kerSmul πB (Submodule.mkQ_surjective _)]

/-- **Induction of a quotient module, modulo a kernel**: `Ind_φ (N / N')` modulo
`ker(π_B) · Ind_φ (N / N')` is `Ind_φ N` modulo `indImageSub φ N' ⊔ ker(π_B) · Ind_φ N`. -/
def indQuotSupEquiv :
    (Ind (N₀ ⧸ S) φ ⧸ indKerSub φ πB (N₀ ⧸ S)) ≃ₗ[B]
      Ind N₀ φ ⧸ (indImageSub φ S ⊔ indKerSub φ πB N₀) :=
  (Submodule.Quotient.equiv (indKerSub φ πB (N₀ ⧸ S))
      ((indKerSub φ πB N₀).map (indImageSub φ S).mkQ) (indModQuotEquiv φ S).symm
      (map_indModQuotEquiv_symm_indKerSub φ πB S)).trans
    (Submodule.quotientQuotientEquivQuotientSup (indImageSub φ S) (indKerSub φ πB N₀))

theorem indQuotSupEquiv_mk (x : Ind N₀ φ) :
    indQuotSupEquiv φ πB S (Submodule.Quotient.mk (Ind.map S.mkQ x)) =
      Submodule.Quotient.mk x := by
  rw [← indModQuotEquiv_mk φ S x]
  show Submodule.quotientQuotientEquivQuotientSup (indImageSub φ S) (indKerSub φ πB N₀)
      (Submodule.Quotient.mk ((indModQuotEquiv φ S).symm
        (indModQuotEquiv φ S (Submodule.Quotient.mk x)))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

end InductionAlong

end

end Categorification
