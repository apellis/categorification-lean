/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlong

/-!
# Exactness of induction along a map with projective corner

Let `φ : A →ₙ+* B` be a nonunital ring map and `Ind N φ = B φ(1) ⊗_A N` induction along it
(`InductionAlong.Ind`). Induction always preserves surjections (`Ind.map_surjective`). When the
corner `B φ(1)` is projective as a right `A`-module, it also preserves injections
(`Ind.map_injective`) and exactness in the middle (`Ind.map_exact`), so it is exact.

The proof uses a dual basis `s` of the corner: `z = ∑_y y · s(z)_y`. The map
`z ⊗ n ↦ (y ↦ s(z)_y n)` embeds `Ind N φ` as a retract of `Corner φ →₀ N`, naturally in `N`
(`Ind.coord`, `Ind.back`, `Ind.back_coord`, `Ind.coord_map`, `Ind.back_mapRange`).

This is the formal input for the exactness of Webster's functor `Fᵢ`
(arXiv:1309.3796v3, §4.6, Theorem 4.31: the corner is projective).
-/

namespace Categorification

open MulOpposite

noncomputable section

namespace InductionAlong

universe u w

variable {A : Type u} [Ring A] {B : Type u} [Ring B] {φ : A →ₙ+* B}

namespace Ind

variable {N : Type w} [AddCommGroup N] [Module A N]
  {N' : Type w} [AddCommGroup N'] [Module A N'] {N'' : Type w} [AddCommGroup N'']
  [Module A N'']

/-- Induction preserves surjections. -/
theorem map_surjective {g : N →ₗ[A] N'} (hg : Function.Surjective g) :
    Function.Surjective (map (φ := φ) g) := by
  intro t
  induction t using induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul z n =>
    obtain ⟨n, rfl⟩ := hg n
    exact ⟨tmul z n, rfl⟩
  | add s t hs ht =>
    obtain ⟨s, rfl⟩ := hs
    obtain ⟨t, rfl⟩ := ht
    exact ⟨s + t, map_add _ _ _⟩

variable (s : Corner φ →ₗ[Aᵐᵒᵖ] (Corner φ →₀ Aᵐᵒᵖ))

/-- The coordinate function `(z, n) ↦ (y ↦ s(z)_y n)`. -/
def coordFun (z : Corner φ) (n : N) : Corner φ →₀ N :=
  (s z).mapRange (fun r => r.unop • n) (by simp)

theorem coordFun_apply (z : Corner φ) (n : N) (y : Corner φ) :
    coordFun s z n y = (s z y).unop • n :=
  Finsupp.mapRange_apply (hf := by simp)

/-- The coordinates `Ind N φ → (Corner φ →₀ N)` attached to `s`. -/
def coord : Ind N φ →+ (Corner φ →₀ N) :=
  liftAdd (coordFun s)
    (fun z z' n => by
      ext y
      simp only [coordFun_apply, map_add, Finsupp.add_apply, unop_add, add_smul])
    (fun z n n' => by
      ext y
      simp only [coordFun_apply, Finsupp.add_apply, smul_add])
    (fun z a n => by
      ext y
      simp only [coordFun_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, unop_mul,
        unop_op, mul_smul])

@[simp] theorem coord_tmul (z : Corner φ) (n : N) : coord s (tmul z n) = coordFun s z n := rfl

variable (N) in
/-- The summation map `(Corner φ →₀ N) → Ind N φ`, `f ↦ ∑_y y ⊗ f(y)`. -/
def back : (Corner φ →₀ N) →+ Ind N φ :=
  Finsupp.liftAddHom fun y => AddMonoidHom.mk' (tmul y) (tmul_add y)

theorem back_single (y : Corner φ) (n : N) : back N (Finsupp.single y n) = tmul y n :=
  Finsupp.liftAddHom_apply_single _ _ _

theorem sum_tmul {X : Type*} (t : Finset X) (z : X → Corner φ) (n : N) :
    tmul (∑ x ∈ t, z x) n = ∑ x ∈ t, tmul (z x) n := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [zero_tmul]
  | insert x t hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, add_tmul, ih]

theorem back_coord (hs : Finsupp.linearCombination Aᵐᵒᵖ id ∘ₗ s = LinearMap.id)
    (t : Ind N φ) : back N (coord s t) = t := by
  induction t using induction_on with
  | zero => rw [map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul z n =>
    rw [coord_tmul, coordFun, back, Finsupp.liftAddHom_apply,
      Finsupp.sum_mapRange_index (fun y => by simp [tmul_zero])]
    have hz : z = (s z).sum fun y r => r • y := by
      have := LinearMap.congr_fun hs z
      rw [LinearMap.comp_apply, Finsupp.linearCombination_apply] at this
      exact this.symm
    conv_rhs => rw [hz]
    rw [Finsupp.sum, Finsupp.sum, sum_tmul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [AddMonoidHom.mk'_apply, ← op_smul_tmul, op_unop]

theorem coord_map (g : N →ₗ[A] N') (t : Ind N φ) :
    coord s (map g t) = Finsupp.mapRange g (map_zero g) (coord s t) := by
  induction t using induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, Finsupp.mapRange_add (map_add g)]
  | tmul z n =>
    ext y
    rw [map_tmul, coord_tmul, coord_tmul, Finsupp.mapRange_apply, coordFun_apply,
      coordFun_apply, map_smul]

theorem back_mapRange (g : N →ₗ[A] N') (f : Corner φ →₀ N) :
    back N' (Finsupp.mapRange g (map_zero g) f) = map g (back N f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => rw [Finsupp.mapRange_add (map_add g), map_add, map_add, map_add, hf, hf']
  | single y n => rw [Finsupp.mapRange_single, back_single, back_single, map_tmul]

/-- Induction along a map whose corner is a projective right module preserves injections. -/
theorem map_injective [Module.Projective Aᵐᵒᵖ (Corner φ)] {g : N →ₗ[A] N'}
    (hg : Function.Injective g) : Function.Injective (map (φ := φ) g) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective Aᵐᵒᵖ (Corner φ)›
  intro x y hxy
  rw [← back_coord s hs x, ← back_coord s hs y]
  congr 1
  apply Finsupp.mapRange_injective g (map_zero g) hg
  rw [← coord_map, ← coord_map, hxy]

/-- Induction along a map whose corner is a projective right module is exact in the middle. -/
theorem map_exact [Module.Projective Aᵐᵒᵖ (Corner φ)] {f : N →ₗ[A] N'} {g : N' →ₗ[A] N''}
    (hfg : Function.Exact f g) : Function.Exact (map (φ := φ) f) (map (φ := φ) g) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective Aᵐᵒᵖ (Corner φ)›
  intro x
  constructor
  · intro hx
    have hmem : ∀ y, coord s x y ∈ Set.range f := fun y => by
      rw [← hfg]
      have := DFunLike.congr_fun (congrArg (coord s) hx) y
      rwa [coord_map, map_zero, Finsupp.mapRange_apply, Finsupp.zero_apply] at this
    choose c hc using hmem
    classical
    let u : Corner φ →₀ N :=
      Finsupp.onFinset (coord s x).support (fun y => if coord s x y = 0 then 0 else c y)
        fun y hy => by
          rw [Finsupp.mem_support_iff]
          intro h
          exact hy (by simp [h])
    refine ⟨back N u, ?_⟩
    rw [← back_mapRange]
    conv_rhs => rw [← back_coord s hs x]
    congr 1
    ext y
    simp only [Finsupp.mapRange_apply, u, Finsupp.onFinset_apply]
    split_ifs with h
    · rw [h, map_zero]
    · exact hc y
  · rintro ⟨y, rfl⟩
    rw [← LinearMap.comp_apply, ← map_comp]
    have : g.comp f = 0 := LinearMap.ext fun m => hfg.apply_apply_eq_zero m
    rw [this]
    induction y using induction_on with
    | zero => simp
    | tmul z n => simp [tmul_zero]
    | add a b ha hb => rw [map_add, ha, hb, add_zero]

end Ind

end InductionAlong

end

end Categorification
