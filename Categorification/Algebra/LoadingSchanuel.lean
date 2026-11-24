/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Module.Projective

/-! # Stable comparison of ordered loading presentations -/

noncomputable section

namespace Categorification.ModuleFiltration

universe u v w p
variable {R : Type u} [Ring R]
variable {P : Type v} {Q : Type w} {X : Type p}
variable [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
  [AddCommGroup X] [Module R X]

private def compatible (f : P →ₗ[R] X) (g : Q →ₗ[R] X) : Submodule R (P × Q) :=
  LinearMap.ker (f.comp (LinearMap.fst R P Q) - g.comp (LinearMap.snd R P Q))

private theorem compatible_eq {f : P →ₗ[R] X} {g : Q →ₗ[R] X} {x : P × Q} :
    x ∈ compatible f g ↔ f x.1 = g x.2 := by
  change f x.1 - g x.2 = 0 ↔ _
  exact sub_eq_zero

/-- A lift of the second presentation into the first splits the common pullback. -/
private def kernelProdEquivCompatible (f : P →ₗ[R] X) (g : Q →ₗ[R] X)
    (lift : Q →ₗ[R] P) (hl : f.comp lift = g) :
    (LinearMap.ker f × Q) ≃ₗ[R] compatible f g := by
  let F : LinearMap.ker f × Q →ₗ[R] compatible f g := {
    toFun := fun x => ⟨(x.1.val + lift x.2, x.2), compatible_eq.mpr (by
      change f (x.1.val + lift x.2) = g x.2
      rw [map_add, show f x.1.val = 0 from x.1.property, zero_add]
      exact LinearMap.congr_fun hl _)⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      apply Prod.ext
      · change (x.1.val + y.1.val) + lift (x.2 + y.2) =
          (x.1.val + lift x.2) + (y.1.val + lift y.2)
        rw [map_add]
        abel
      · rfl
    map_smul' := by
      intro a x
      apply Subtype.ext
      apply Prod.ext
      · change a • x.1.val + lift (a • x.2) = a • (x.1.val + lift x.2)
        rw [map_smul, smul_add]
      · rfl }
  refine LinearEquiv.ofBijective F ⟨?_, ?_⟩
  · intro x y he
    have hp := congrArg Subtype.val he
    have hq : x.2 = y.2 := congrArg (fun z : P × Q => z.2) hp
    refine Prod.ext (Subtype.ext ?_) hq
    have hr : x.1.val + lift x.2 = y.1.val + lift y.2 := congrArg (fun z : P × Q => z.1) hp
    rw [hq] at hr
    exact add_right_cancel hr
  · intro x
    have hf : f (x.1.1 - lift x.1.2) = 0 := by
      have h : f (lift x.1.2) = g x.1.2 := LinearMap.congr_fun hl _
      rw [map_sub, compatible_eq.mp x.property, h, sub_self]
    refine ⟨(⟨_, hf⟩, x.1.2), Subtype.ext (Prod.ext ?_ rfl)⟩
    change x.1.1 - lift x.1.2 + lift x.1.2 = x.1.1
    exact sub_add_cancel _ _

/-- Interchanging the two presentations preserves the common pullback. -/
private def compatibleSymm (f : P →ₗ[R] X) (g : Q →ₗ[R] X) :
    compatible f g ≃ₗ[R] compatible g f where
  toFun x := ⟨x.val.swap, compatible_eq.mpr (compatible_eq.mp x.property).symm⟩
  invFun x := ⟨x.val.swap, compatible_eq.mpr (compatible_eq.mp x.property).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Schanuel's comparison for two surjective projective presentations of the same
syzygy, as used to replace the covers in Webster, arXiv:1309.3796v2, Lemma 6.11.
It retains the individual two projective terms rather than a class in K₀. -/
theorem exists_kernelProdEquiv_of_projective_presentations (f : P →ₗ[R] X) (g : Q →ₗ[R] X)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    [Module.Projective R P] [Module.Projective R Q] :
    Nonempty ((LinearMap.ker f × Q) ≃ₗ[R] (LinearMap.ker g × P)) := by
  obtain ⟨u, hu⟩ := Module.projective_lifting_property f g hf
  obtain ⟨v, hv⟩ := Module.projective_lifting_property g f hg
  exact ⟨(kernelProdEquivCompatible f g u hu).trans
    ((compatibleSymm f g).trans (kernelProdEquivCompatible g f v hv).symm)⟩


section Stable

variable {P₀ Q₀ X₀ Y₀ A B : Type u}
variable [AddCommGroup P₀] [Module R P₀] [AddCommGroup Q₀] [Module R Q₀]
  [AddCommGroup X₀] [Module R X₀] [AddCommGroup Y₀] [Module R Y₀]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

theorem projectiveProduct {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Projective R M] [Module.Projective R N] :
    Module.Projective R (M × N) := by
  apply Module.Projective.of_lifting_property
  intro S T _ _ _ _ f g hf
  obtain ⟨p, hp⟩ := Module.projective_lifting_property f (g.comp (LinearMap.inl R M N)) hf
  obtain ⟨q, hq⟩ := Module.projective_lifting_property f (g.comp (LinearMap.inr R M N)) hf
  refine ⟨p.coprod q, ?_⟩
  apply LinearMap.ext
  rintro ⟨x,y⟩
  change f (p x + q y) = g (x,y)
  rw [map_add, show f (p x) = g (x,0) from LinearMap.congr_fun hp x,
    show f (q y) = g (0,y) from LinearMap.congr_fun hq y, ← map_add]
  congr 1
  simp

private def kernelProdId (f : P₀ →ₗ[R] X₀) (E : (X₀ × A) ≃ₗ[R] (Y₀ × B)) :
    LinearMap.ker (E.toLinearMap.comp (f.prodMap (LinearMap.id : A →ₗ[R] A))) ≃ₗ[R]
      LinearMap.ker f where
  toFun x := ⟨x.val.1, congrArg Prod.fst (E.map_eq_zero_iff.mp x.property)⟩
  invFun x := ⟨(x.val, 0), E.map_eq_zero_iff.mpr (Prod.ext x.property rfl)⟩
  left_inv x := Subtype.ext (Prod.ext rfl
    (congrArg Prod.snd (E.map_eq_zero_iff.mp x.property)).symm)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Stable comparison of the next syzygies in two resolutions. The auxiliary
projectives in the input remain individual summands on the output. -/
theorem exists_stable_kernelEquiv (E : (X₀ × A) ≃ₗ[R] (Y₀ × B))
    (f : P₀ →ₗ[R] X₀) (g : Q₀ →ₗ[R] Y₀)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    [Module.Projective R P₀] [Module.Projective R Q₀]
    [Module.Projective R A] [Module.Projective R B] :
    Nonempty ((LinearMap.ker f × (Q₀ × B)) ≃ₗ[R] (LinearMap.ker g × (P₀ × A))) := by
  let F := E.toLinearMap.comp (f.prodMap (LinearMap.id : A →ₗ[R] A))
  let G := (LinearEquiv.refl R (Y₀ × B)).toLinearMap.comp
    (g.prodMap (LinearMap.id : B →ₗ[R] B))
  have hF : Function.Surjective F :=
    E.surjective.comp (fun ⟨x, a⟩ => let ⟨p, hp⟩ := hf x; ⟨(p, a), Prod.ext hp rfl⟩)
  have hG : Function.Surjective G := fun ⟨x, b⟩ =>
    let ⟨q, hq⟩ := hg x; ⟨(q, b), Prod.ext hq rfl⟩
  let : Module.Projective R (P₀ × A) := projectiveProduct
  let : Module.Projective R (Q₀ × B) := projectiveProduct
  obtain ⟨H⟩ := exists_kernelProdEquiv_of_projective_presentations F G hF hG
  exact ⟨((kernelProdId f E).symm.prodCongr (LinearEquiv.refl R _)).trans
    (H.trans ((kernelProdId g (LinearEquiv.refl R _)).prodCongr (LinearEquiv.refl R _)))⟩


variable {ι : Type*} (e : ι → R)

/-- The selected loading idempotents generate the module through their fixed vectors. -/
def FixedLoadingSpan (M : Type*) [AddCommGroup M] [Module R M] : Prop :=
  ∀ x : M, x ∈ Submodule.span R {y | ∃ i, e i • y = y}

/-- Loading generation passes through a surjective linear map. -/
theorem FixedLoadingSpan.map (F : X₀ →ₗ[R] Y₀) (hF : Function.Surjective F)
    (h : FixedLoadingSpan e X₀) : FixedLoadingSpan e Y₀ := by
  intro y
  obtain ⟨x, rfl⟩ := hF y
  have hs : Submodule.span R {y : X₀ | ∃ i, e i • y = y} ≤
      (Submodule.span R {y : Y₀ | ∃ i, e i • y = y}).comap F := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, hx⟩
    exact Submodule.subset_span ⟨i, by rw [← map_smul, hx]⟩
  exact hs (h x)

/-- Loading generation is preserved by adjoining an independently supported summand. -/
theorem FixedLoadingSpan.prod (hX : FixedLoadingSpan e X₀) (hA : FixedLoadingSpan e A) :
    FixedLoadingSpan e (X₀ × A) := by
  intro x
  let S := Submodule.span R {y : X₀ × A | ∃ i, e i • y = y}
  have h₁ : Submodule.span R {y : X₀ | ∃ i, e i • y = y} ≤
      S.comap (LinearMap.inl R X₀ A) := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, hx⟩
    exact Submodule.subset_span ⟨i, Prod.ext hx (smul_zero _)⟩
  have h₂ : Submodule.span R {y : A | ∃ i, e i • y = y} ≤
      S.comap (LinearMap.inr R X₀ A) := by
    apply Submodule.span_le.mpr
    rintro a ⟨i, ha⟩
    exact Submodule.subset_span ⟨i, Prod.ext (smul_zero _) ha⟩
  simpa using S.add_mem (h₁ (hX x.1)) (h₂ (hA x.2))

/-- Supported auxiliary terms on the comparison side suffice to transfer generation
from an ordinary syzygy to a stably equivalent graded syzygy. -/
theorem FixedLoadingSpan.of_stableEquiv (E : (X₀ × A) ≃ₗ[R] (Y₀ × B))
    (hY : FixedLoadingSpan e Y₀) (hB : FixedLoadingSpan e B) : FixedLoadingSpan e X₀ :=
  (hY.prod e hB).map e ((LinearMap.fst R X₀ A).comp E.symm.toLinearMap)
    (fun x => ⟨E (x, 0), by simp⟩)

end Stable

end Categorification.ModuleFiltration
