/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SimpleTopGrading

/-!
# Recovering a simple factor from its head

Webster, arXiv:1309.3796v2, proof of Theorem 5.8 after Lemma 5.9.
Generating an induced module on its maximal cut and taking its head
preserves the original simple on that cut. Operators killing the induced
module continue to kill the head.
-/

noncomputable section
namespace Categorification.Stendhal
open Categorification.Graded GProj

variable {k A B C : Type*} [Field k] [Ring A] [Ring B] [Ring C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B}
    (q : A →ₐ[k] C) (φ : B →ₙₐ[k] C)

/-- An occurrence of the simple over the factor algebra as the entire
maximal cut of an ambient simple, with the action computed in the layer. -/
structure CornerTopRestriction (b : IndecClass ℬ) (s : IndecClass 𝒜) where
  /-- Inclusion of the factor simple. -/
  incl : b.top →ₗ[k] s.top
  injective : Function.Injective incl
  intertwines : ∀ (a : A) (t : B), q a = φ t → ∀ x, a • incl x = incl (t • x)
  fixed : ∀ (a : A), q a = φ 1 → ∀ x : s.top, a • x = x → ∃ z, incl z=x

theorem CornerTopRestriction.eq [GradedAlgebra ℬ] [HasGdim ℬ] [Module.Finite k B]
    (hq : Function.Surjective q) {b c : IndecClass ℬ} {s : IndecClass 𝒜}
    (f : CornerTopRestriction q φ b s) (g : CornerTopRestriction q φ c s) : b=c := by
  let := (IndecClass.isGradedSimple_top b).nontrivial
  obtain ⟨x,hx⟩ := exists_ne (0 : b.top)
  obtain ⟨a,ha⟩ := hq (φ 1)
  obtain ⟨y,hy⟩ := g.fixed a ha (f.incl x) (by rw [f.intertwines a 1 ha,one_smul])
  have hn : y ≠ 0 := fun hz => hx (f.injective (by rw [← hy,hz,map_zero,map_zero]))
  apply indecClass_eq_of_corner_annihilator (e := 1) hx hn (one_smul _ _) (one_smul _ _)
  intro t ht
  obtain ⟨z,hz⟩ := hq (φ (1*t*1))
  apply g.injective
  rw [← g.intertwines z _ hz,hy,f.intertwines z _ hz,ht,map_zero,map_zero]

variable (M : Type*) [AddCommGroup M] [Module k M] [Module C M] [IsScalarTower k C M]
private abbrev cornerSpan := Submodule.span C {x : M | φ 1 • x = x}
local notation "P" => cornerSpan φ M
local notation "F" => boundaryFixed φ M
local notation "Fₚ" => boundaryFixed φ (P)

/-- Generating on a cut preserves its fixed vectors. -/
private def spanFixedEquiv : F ≃ₗ[B] Fₚ where
  toFun x := ⟨⟨x.1,Submodule.subset_span x.2⟩,Subtype.ext x.2⟩
  invFun x := ⟨x.1.1,congrArg Subtype.val x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Module k M] [IsScalarTower k C M] in
private theorem spanFixed_generates : Submodule.span C {x : P | φ 1 • x = x} = ⊤ := by
  let W := Submodule.span C {x : P | φ 1 • x = x}
  have h : P ≤ W.map (P).subtype := by
    apply Submodule.span_le.mpr
    intro x hx
    let y : P := ⟨x,Submodule.subset_span hx⟩
    exact ⟨y,Submodule.subset_span (show φ 1 • y = y from Subtype.ext hx),rfl⟩
  apply Submodule.eq_top_iff'.mpr
  intro y
  obtain ⟨z,hz,he⟩ := h y.2
  exact (Subtype.ext he : z=y) ▸ hz

/-- From any representation whose cut is the specified simple, take the
submodule generated on the cut and its unique head. It retains the whole
factor simple and inherits every annihilator of the representation. The
induced representation itself can be supplied ungraded. -/
theorem exists_cornerHeadRestriction [GradedAlgebra 𝒜] [HasGdim 𝒜] [Module.Finite k A]
    (hq : Function.Surjective q) (b : IndecClass ℬ) [IsSimpleModule B b.top]
    (f : b.top ≃ₗ[B] F) :
    ∃ s : IndecClass 𝒜, Nonempty (CornerTopRestriction q φ b s) ∧
      ∀ a : A, (∀ x : M, q a • x = 0) → ∀ y : s.top, a • y = 0 := by
  let g := f.trans (spanFixedEquiv φ M)
  let := IsSimpleModule.congr g.symm
  let K := cornerKernel (φ 1) (P)
  let H := (P) ⧸ K
  let : IsSimpleModule C H := (eq_cornerKernel_iff_simpleQuotient (P) φ (spanFixed_generates φ M) K).mp rfl
  let : Module A H := Module.compHom H q.toRingHom
  have act (a : A) (x : H) : a • x = q a • x := rfl
  let : IsScalarTower k A H := ⟨fun c a x => by rw [act,act,map_smul,smul_assoc]⟩
  let : IsSimpleModule A H := isSimpleModule_iff_toSpanSingleton_surjective.mpr
    ⟨IsSimpleModule.nontrivial C H,by
      intro x hx y
      obtain ⟨t,ht⟩ := IsSimpleModule.toSpanSingleton_surjective C hx y
      obtain ⟨a,rfl⟩ := hq t
      exact ⟨a,ht⟩⟩
  obtain ⟨s,⟨h⟩⟩ := exists_indecClass_of_simple 𝒜 H
  let j : b.top ≃ₗ[B] boundaryFixed φ H := g.trans (cornerHeadFixedEquiv (P) φ)
  let ι : b.top →ₗ[k] s.top := (h.toLinearMap.restrictScalars k).comp
    ((idemSubspace k H (φ 1)).subtype.comp (j.toLinearMap.restrictScalars k))
  have hι (x : b.top) : ι x = h (j x).1 := rfl
  refine ⟨s,⟨⟨ι,fun x y he => j.injective (Subtype.ext (h.injective he)),?_,?_⟩⟩,?_⟩
  · intro a t ht x
    rw [hι,hι,← h.map_smul a,act a,ht,j.map_smul]
    rfl
  · intro a ha x hx
    let y := h.symm x
    have hy : φ 1 • y = y := by
      rw [← ha,← act,← h.symm.map_smul,hx]
    refine ⟨j.symm ⟨y,hy⟩,?_⟩
    exact (congrArg h (congrArg Subtype.val (j.apply_symm_apply ⟨y,hy⟩))).trans (h.apply_symm_apply x)
  · intro a ha y
    obtain ⟨v,rfl⟩ := h.surjective y
    obtain ⟨w,rfl⟩ := K.mkQ_surjective v
    rw [← h.map_smul,act,← K.mkQ.map_smul,
      show q a • w = 0 from Subtype.ext (ha w.1),map_zero,map_zero]

end Categorification.Stendhal
