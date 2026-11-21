/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.BaseChange

/-!
# Extension of scalars for KLR algebras

Let `φ : k → k'` be a homomorphism of commutative rings carrying the KLR polynomials `Q` to `Q'`
off the diagonal, and let `B` be a `k'`-algebra. A ring homomorphism `g : R_k(ν) → B` that is
compatible with `φ` on scalars extends uniquely to a `k'`-algebra homomorphism
`R_{k'}(ν) → B` sending each generator `e(𝐢)`, `x_a`, `ψ_j` to the image under `g` of the
generator of the same name (`KLRAlgebra.extendScalars`). Its composite with the change of base
ring `R_k(ν) → R_{k'}(ν)` (`KLRAlgebra.mapRingHom`) is `g`. This is the extension-of-scalars
property of the KLR algebras of Khovanov–Lauda and Rouquier: `R_{k'}(ν)` is generated over `k'`
by the images of the generators of `R_k(ν)`, subject to the same relations.
-/

namespace Categorification.KLR

open MvPolynomial

variable {I : Type*} [DecidableEq I] {k k' : Type*} [CommRing k] [CommRing k']

namespace KLRAlgebra

section extendScalars

variable (φ : k →+* k') {Q : I → I → MvPolynomial (Fin 2) k}
  {Q' : I → I → MvPolynomial (Fin 2) k'}
  (hQ : ∀ a b, a ≠ b → MvPolynomial.map φ (Q a b) = Q' a b) {ν : Multiset I}
  {B : Type*} [Ring B] [Algebra k' B] (g : KLRAlgebra k Q ν →+* B)
  (hg : ∀ c, g (algebraMap k _ c) = algebraMap k' B (φ c))

/-- The images in `B` of the generators. -/
noncomputable def extGenImg : Gen ν → B
  | .idem i => g (e i)
  | .dot a => g (x a)
  | .cross j => g (ψ j)

/-- The free `k'`-algebra on the generators maps to `B`. -/
noncomputable def extFree : FreeAlgebra k' (Gen ν) →ₐ[k'] B :=
  FreeAlgebra.lift k' (extGenImg g)

theorem extFree_ι (t : Gen ν) : extFree g (FreeAlgebra.ι k' t) = extGenImg g t :=
  FreeAlgebra.lift_ι_apply _ _

include hQ hg in
theorem extFree_rel ⦃u v : FreeAlgebra k' (Gen ν)⦄ (h : Rel k' Q' ν u v) :
    extFree g u = extFree g v := by
  have hfe : ∀ i, extFree g (fe k' ν i) = g (e i) := fun i => extFree_ι g _
  have hfx : ∀ a, extFree g (fx k' ν a) = g (x a) := fun a => extFree_ι g _
  have hfψ : ∀ j, extFree g (fψ k' ν j) = g (ψ j) := fun j => extFree_ι g _
  have hnc : ∀ {n : ℕ} (y : Fin n → FreeAlgebra k' (Gen ν)) (p : MvPolynomial (Fin n) k'),
      extFree g (ncEval y p) = ncEval (fun a => extFree g (y a)) p := by
    intro n y p
    have := map_ncEval (RingHom.id k') (extFree g).toRingHom
      (fun c => (extFree g).commutes c) y p
    rwa [MvPolynomial.map_id] at this
  cases h with
  | idem_mul i j =>
    rw [map_mul, hfe, hfe, ← map_mul, e_mul_e]
    split_ifs <;> simp [hfe]
  | idem_sum =>
    rw [map_sum, map_one]; simp only [hfe]; rw [← map_sum, sum_e, map_one]
  | dot_idem a i =>
    rw [map_mul, map_mul, hfe, hfx, ← map_mul, ← map_mul, x_mul_e a i]
  | cross_idem j i =>
    rw [map_mul, map_mul, hfe, hfe, hfψ, ← map_mul, ← map_mul, ψ_mul_e j i]
  | cross_zero j h => rw [map_zero, hfψ, ψ_eq_zero j h, map_zero]
  | dot_dot a b => rw [map_mul, map_mul, hfx, hfx, ← map_mul, ← map_mul, x_mul_x a b]
  | cross_cross j l h =>
    rw [map_mul, map_mul, hfψ, hfψ, ← map_mul, ← map_mul, ψ_mul_ψ j l h]
  | dot_cross a j h₁ h₂ =>
    rw [map_mul, map_mul, hfx, hfψ, ← map_mul, ← map_mul, x_mul_ψ a j h₁ h₂]
  | dot_cross_left j h i =>
    rw [map_mul, map_sub, map_mul, map_mul, hfx, hfx, hfψ, hfe, ← map_mul, ← map_mul,
      ← map_sub, ← map_mul, dot_cross_left]
    split_ifs <;> simp [hfe]
  | dot_cross_right j h i =>
    rw [map_mul, map_sub, map_mul, map_mul, hfx, hfx, hfψ, hfe, ← map_mul, ← map_mul,
      ← map_sub, ← map_mul, dot_cross_right]
    split_ifs <;> simp [hfe]
  | cross_sq j h i =>
    rw [map_mul, map_mul, hfψ, hfe, ← map_mul, ← map_mul, ψ_sq j h i]
    split_ifs with hc
    · simp
    · rw [map_mul, map_mul, hfe, hnc, map_ncEval φ g hg, hQ _ _ hc]
      congr 2
      funext a; fin_cases a <;> simp [hfx]
  | braid j h i =>
    rw [map_mul, map_sub, map_mul, map_mul, map_mul, map_mul, hfψ, hfψ, hfe, ← map_mul,
      ← map_mul, ← map_mul, ← map_mul, ← map_sub, ← map_mul, braid j h i]
    split_ifs with hc
    · rw [map_mul, map_mul, hfe, hnc, map_ncEval φ g hg, map_qbar, hQ _ _ hc.2]
      congr 2
      funext a; fin_cases a <;> simp [hfx]
    · simp

/-- **Extension of scalars**: a ring homomorphism `g : R_k(ν) → B` into a `k'`-algebra,
compatible with `φ : k → k'` on scalars, extends to a `k'`-algebra homomorphism
`R_{k'}(ν) → B` sending each generator to the image under `g` of the generator of the same
name. -/
noncomputable def extendScalars : KLRAlgebra k' Q' ν →ₐ[k'] B :=
  RingQuot.liftAlgHom k' ⟨extFree g, extFree_rel φ hQ g hg⟩

theorem extendScalars_mk (u : FreeAlgebra k' (Gen ν)) :
    extendScalars φ hQ g hg (mk k' Q' ν u) = extFree g u :=
  RingQuot.liftAlgHom_mkAlgHom_apply k' _ _ u

/-- `extendScalars` on the idempotent generators. -/
@[simp] theorem extendScalars_e (i : Seq ν) :
    extendScalars φ hQ g hg (e i) = g (e i) := by
  rw [e, extendScalars_mk]; exact extFree_ι g _

/-- `extendScalars` on the dot generators. -/
@[simp] theorem extendScalars_x (a : Fin (Multiset.card ν)) :
    extendScalars φ hQ g hg (x a) = g (x a) := by
  rw [x, extendScalars_mk]; exact extFree_ι g _

/-- `extendScalars` on the crossing generators. -/
@[simp] theorem extendScalars_ψ (j : ℕ) :
    extendScalars φ hQ g hg (ψ j) = g (ψ j) := by
  rw [ψ, extendScalars_mk]; exact extFree_ι g _

/-- Two `k'`-algebra homomorphisms out of `R_{k'}(ν)` agreeing on all generators are equal. -/
theorem extendScalars_ext {f₁ f₂ : KLRAlgebra k' Q' ν →ₐ[k'] B}
    (he : ∀ i, f₁ (e i) = f₂ (e i)) (hx : ∀ a, f₁ (x a) = f₂ (x a))
    (hψ : ∀ j, f₁ (ψ j) = f₂ (ψ j)) : f₁ = f₂ := by
  have hmk : f₁.comp (mk k' Q' ν) = f₂.comp (mk k' Q' ν) := by
    refine FreeAlgebra.hom_ext (funext fun t => ?_)
    cases t with
    | idem i => exact he i
    | dot a => exact hx a
    | cross j => exact hψ j
  exact RingQuot.ringQuot_ext' k' f₁ f₂ hmk

/-- The extension composed with the change of base ring `R_k(ν) → R_{k'}(ν)` is `g`. -/
theorem extendScalars_mapRingHom (r : KLRAlgebra k Q ν) :
    extendScalars φ hQ g hg (mapRingHom φ hQ r) = g r := by
  obtain ⟨u, rfl⟩ := mk_surjective r
  have h : ((extendScalars φ hQ g hg).toRingHom.comp (mapRingHom φ hQ)).comp
      (mk k Q ν).toRingHom = g.comp (mk k Q ν).toRingHom := by
    refine RingHom.ext fun w => ?_
    induction w using FreeAlgebra.induction with
    | grade0 c =>
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        AlgHom.commutes, mapRingHom_algebraMap, hg]
    | grade1 t =>
      cases t with
      | idem i => exact (congrArg _ (mapRingHom_e φ hQ i)).trans (extendScalars_e φ hQ g hg i)
      | dot a => exact (congrArg _ (mapRingHom_x φ hQ a)).trans (extendScalars_x φ hQ g hg a)
      | cross j => exact (congrArg _ (mapRingHom_ψ φ hQ j)).trans (extendScalars_ψ φ hQ g hg j)
    | mul a b ha hb => simp only [map_mul] at ha hb ⊢; rw [ha, hb]
    | add a b ha hb => simp only [map_add] at ha hb ⊢; rw [ha, hb]
  exact RingHom.congr_fun h u

end extendScalars

end KLRAlgebra

end Categorification.KLR
