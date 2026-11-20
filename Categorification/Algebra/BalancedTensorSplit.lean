/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.BalancedTensor

/-!
# Split exact sequences of right modules stay exact after `- ⊗_A N`

For a right `A`-linear map `f : M → M'` (a `k`-linear map commuting with the right action of
`A`) the map `f ⊗ 1 : M ⊗_A N → M' ⊗_A N` (`BalancedTensor.mapLeftOp`) is defined. If
`M₁ →f M₂ →g M₃ → 0` is exact and `f` has a right `A`-linear left inverse, then
`0 → M₁ ⊗_A N → M₂ ⊗_A N → M₃ ⊗_A N → 0` is exact for every left `A`-module `N`
(`mapLeftOp_injective_of_leftInverse`, `exists_mapLeftOp_eq_of_mapLeftOp_eq_zero`,
`mapLeftOp_surjective`). This is used for the split sequence of Kang–Kashiwara, arXiv:1102.4677v4,
Theorem 4.5, in the proof of Webster, arXiv:1309.3796v3, Proposition 5.5.
-/

open MulOpposite
open scoped TensorProduct

noncomputable section

namespace Categorification.BalancedTensor

variable {k : Type*} [CommRing k] {B : Type*} [Ring B] [Algebra k B] {A : Type*} [Ring A]
  {N : Type*} [AddCommGroup N] [Module k N] [Module A N]

section MapLeft

variable {M M' M'' : Type*}
  [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M] [Module Aᵐᵒᵖ M]
  [SMulCommClass B Aᵐᵒᵖ M]
  [AddCommGroup M'] [Module k M'] [Module B M'] [IsScalarTower k B M'] [Module Aᵐᵒᵖ M']
  [SMulCommClass B Aᵐᵒᵖ M']
  [AddCommGroup M''] [Module k M''] [Module B M''] [IsScalarTower k B M''] [Module Aᵐᵒᵖ M'']
  [SMulCommClass B Aᵐᵒᵖ M'']

variable (B N) in
/-- The map `M ⊗_A N → M' ⊗_A N` induced by a right `A`-linear `k`-linear map `f : M → M'`. -/
def mapLeftOp (f : M →ₗ[k] M') (hf : ∀ (a : A) (m : M), f (op a • m) = op a • f m) :
    BalancedTensor k B A M N →ₗ[k] BalancedTensor k B A M' N :=
  lift ((mkBil k B A M' N).comp f) (fun m a n => by
    simp only [LinearMap.comp_apply, mkBil_apply, hf, op_smul_tmul])

omit [SMulCommClass B Aᵐᵒᵖ M'] in
@[simp] theorem mapLeftOp_tmul (f : M →ₗ[k] M') (hf : ∀ (a : A) (m : M), f (op a • m) = op a • f m)
    (m : M) (n : N) : mapLeftOp B N f hf (tmul m n) = tmul (f m) n := rfl

omit [SMulCommClass B Aᵐᵒᵖ M''] in
theorem mapLeftOp_comp (f : M →ₗ[k] M') (hf : ∀ (a : A) (m : M), f (op a • m) = op a • f m)
    (g : M' →ₗ[k] M'') (hg : ∀ (a : A) (m : M'), g (op a • m) = op a • g m)
    (x : BalancedTensor k B A M N) :
    mapLeftOp B N g hg (mapLeftOp B N f hf x) =
      mapLeftOp B N (g ∘ₗ f) (fun a m => by rw [LinearMap.comp_apply, hf, hg]; rfl) x := by
  induction x using induction_on with
  | zero => simp
  | tmul m n => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

omit [SMulCommClass B Aᵐᵒᵖ M'] in
theorem mapLeftOp_add (f f' : M →ₗ[k] M') (hf : ∀ (a : A) (m : M), f (op a • m) = op a • f m)
    (hf' : ∀ (a : A) (m : M), f' (op a • m) = op a • f' m) (x : BalancedTensor k B A M N) :
    mapLeftOp B N (f + f') (fun a m => by
      rw [LinearMap.add_apply, LinearMap.add_apply, hf, hf', smul_add]) x =
      mapLeftOp B N f hf x + mapLeftOp B N f' hf' x := by
  induction x using induction_on with
  | zero => simp
  | tmul m n => rw [mapLeftOp_tmul, mapLeftOp_tmul, mapLeftOp_tmul, LinearMap.add_apply, add_tmul]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; abel

theorem mapLeftOp_id (x : BalancedTensor k B A M N) :
    mapLeftOp B N (LinearMap.id : M →ₗ[k] M) (fun _ _ => rfl) x = x := by
  induction x using induction_on with
  | zero => simp
  | tmul m n => rfl
  | add x y hx hy => rw [map_add, hx, hy]

omit [SMulCommClass B Aᵐᵒᵖ M'] in
/-- `f ⊗ 1` is `B`-linear when `f` is. -/
theorem mapLeftOp_smul (f : M →ₗ[k] M') (hf : ∀ (a : A) (m : M), f (op a • m) = op a • f m)
    (hB : ∀ (b : B) (m : M), f (b • m) = b • f m) (b : B) (x : BalancedTensor k B A M N) :
    mapLeftOp B N f hf (b • x) = b • mapLeftOp B N f hf x := by
  induction x using induction_on with
  | zero => simp
  | tmul m n => rw [smul_tmul', mapLeftOp_tmul, mapLeftOp_tmul, hB, smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- A right `A`-linear map with a right `A`-linear left inverse stays injective after `- ⊗_A N`. -/
theorem mapLeftOp_injective_of_leftInverse (f : M →ₗ[k] M')
    (hf : ∀ (a : A) (m : M), f (op a • m) = op a • f m) (s : M' →ₗ[k] M)
    (hs : ∀ (a : A) (m : M'), s (op a • m) = op a • s m) (hsf : ∀ m, s (f m) = m) :
    Function.Injective (mapLeftOp B N f hf) := by
  intro x y hxy
  have key : ∀ z : BalancedTensor k B A M N, mapLeftOp B N s hs (mapLeftOp B N f hf z) = z := by
    intro z
    rw [mapLeftOp_comp]
    have : s ∘ₗ f = LinearMap.id := LinearMap.ext hsf
    simp only [this]
    exact mapLeftOp_id z
  rw [← key x, ← key y, hxy]

omit [SMulCommClass B Aᵐᵒᵖ M'] in
theorem mapLeftOp_surjective (g : M →ₗ[k] M') (hg : ∀ (a : A) (m : M), g (op a • m) = op a • g m)
    (hsurj : Function.Surjective g) : Function.Surjective (mapLeftOp B N g hg) := by
  intro x
  induction x using induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul m n =>
    obtain ⟨m, rfl⟩ := hsurj m
    exact ⟨tmul m n, rfl⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩

/-- **Exactness in the middle**: if `M →f M' →g M'' → 0` is exact and `f` has a right
`A`-linear left inverse, then `ker (g ⊗ 1) = im (f ⊗ 1)`. -/
theorem exists_mapLeftOp_eq_of_mapLeftOp_eq_zero (f : M →ₗ[k] M')
    (hf : ∀ (a : A) (m : M), f (op a • m) = op a • f m) (s : M' →ₗ[k] M)
    (hs : ∀ (a : A) (m : M'), s (op a • m) = op a • s m) (hsf : ∀ m, s (f m) = m)
    (g : M' →ₗ[k] M'') (hg : ∀ (a : A) (m : M'), g (op a • m) = op a • g m)
    (hsurj : Function.Surjective g) (hker : ∀ m, g m = 0 → ∃ z, f z = m)
    {x : BalancedTensor k B A M' N} (hx : mapLeftOp B N g hg x = 0) :
    ∃ y, mapLeftOp B N f hf y = x := by
  -- `p = 1 - f s` kills `ker g`, so it factors as `h ∘ g`.
  set p : M' →ₗ[k] M' := LinearMap.id - f ∘ₗ s with hp
  have hpker : LinearMap.ker g ≤ LinearMap.ker p := by
    intro m hm
    obtain ⟨z, rfl⟩ := hker m hm
    simp [hp, hsf]
  let h : M'' →ₗ[k] M' :=
    (LinearMap.ker g).liftQ p hpker ∘ₗ (g.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hhg : ∀ m, h (g m) = p m := by
    intro m
    change (LinearMap.ker g).liftQ p hpker
      ((g.quotKerEquivOfSurjective hsurj).symm (g m)) = p m
    rw [show (g.quotKerEquivOfSurjective hsurj).symm (g m) = Submodule.Quotient.mk m from
      (LinearEquiv.symm_apply_eq _).2 rfl]
    rfl
  have hpA : ∀ (a : A) (m : M'), p (op a • m) = op a • p m := by
    intro a m
    simp [hp, hf, hs, smul_sub]
  have hh : ∀ (a : A) (m : M''), h (op a • m) = op a • h m := by
    intro a m
    obtain ⟨m, rfl⟩ := hsurj m
    rw [← hg, hhg, hhg, hpA]
  have hfs : ∀ (a : A) (m : M'), (f ∘ₗ s) (op a • m) = op a • (f ∘ₗ s) m := by
    intro a m
    rw [LinearMap.comp_apply, hs, hf]; rfl
  have hdec : f ∘ₗ s + p = LinearMap.id := by simp [hp]
  have hpx : mapLeftOp B N p hpA x = 0 := by
    have : h ∘ₗ g = p := LinearMap.ext hhg
    have e := mapLeftOp_comp (B := B) (N := N) g hg h hh x
    rw [hx, map_zero] at e
    simp only [this] at e
    exact e.symm
  refine ⟨mapLeftOp B N s hs x, ?_⟩
  rw [mapLeftOp_comp]
  have e := mapLeftOp_add (B := B) (N := N) (f ∘ₗ s) p hfs hpA x
  simp only [hdec] at e
  rw [mapLeftOp_id, hpx, add_zero] at e
  exact e.symm

end MapLeft

end Categorification.BalancedTensor
