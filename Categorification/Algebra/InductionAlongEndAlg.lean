/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTensorFactorAction

/-!
# Induction on endomorphisms

For a `k`-linear nonunital ring map `φ : A → B` of `k`-algebras and an `A`-module `N`, induction
carries `A`-linear endomorphisms of `N` to `B`-linear endomorphisms of `B φ(1) ⊗_A N`
multiplicatively (`IndK.endAlg`), so an action of an algebra `C` on `N` by `A`-linear maps
induces one on the induced module. In B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v3, proof of Proposition 5.5, this carries the action of the last
cyclotomic factor through the functors `Fᵢ`.
-/

noncomputable section

namespace Categorification

namespace InductionAlong

universe u w

variable {k : Type*} [CommRing k] {A : Type u} [Ring A] [Algebra k A] {B : Type u} [Ring B]
  [Algebra k B] (φ : A →ₙ+* B) (N : Type w) [AddCommGroup N] [Module A N] [Module k N]
  [IsScalarTower k A N]

instance IndK.smulCommClass : SMulCommClass B k (IndK k N φ) where
  smul_comm b c x := by
    change b • (algebraMap k B c • x) = algebraMap k B c • (b • x)
    rw [← mul_smul, ← mul_smul, Algebra.commutes]

omit [Algebra k A] [Module k N] [IsScalarTower k A N] in
theorem IndK.map_add' (g g' : Module.End A N) :
    (IndK.map (φ := φ) (k := k) (g + g') : Module.End B (IndK k N φ)) =
      IndK.map g + IndK.map g' :=
  Ind.ext fun z n => Ind.tmul_add z (g n) (g' n)

omit [Algebra k A] [Module k N] [IsScalarTower k A N] in
theorem IndK.map_zero' :
    (IndK.map (φ := φ) (k := k) (0 : Module.End A N) : Module.End B (IndK k N φ)) = 0 :=
  Ind.ext fun z _ => Ind.tmul_zero z

variable (hφ : ∀ (c : k) (t : A), φ (c • t) = c • φ t)

/-- **Induction on endomorphisms**, as a map of `k`-algebras. -/
def IndK.endAlg : Module.End A N →ₐ[k] Module.End B (IndK k N φ) where
  toFun g := IndK.map g
  map_one' := Ind.map_id
  map_mul' g g' := Ind.map_comp g' g
  map_zero' := IndK.map_zero' φ N
  map_add' g g' := IndK.map_add' φ N g g'
  commutes' c := Ind.ext fun z n => by
      change Ind.tmul z (algebraMap k (Module.End A N) c n) =
        algebraMap k (Module.End B (IndK k N φ)) c (Ind.tmul z n)
      rw [Module.algebraMap_end_apply]
      exact Ind.tmul_algebraMap_smul k hφ z c n

@[simp] theorem IndK.endAlg_apply (g : Module.End A N) :
    IndK.endAlg φ N hφ g = IndK.map g := rfl

section Comm

variable {k : Type*} [CommRing k] {A : Type u} [Ring A] {B : Type u} [Ring B] [Algebra k B]
  {φ : A →ₙ+* B} {N N' : Type w} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']

/-- **Induction of a commuting square**: if `e ∘ g = g' ∘ e`, then the same holds after
induction. -/
theorem IndK.map_comm_apply {g : N →ₗ[A] N} {g' : N' →ₗ[A] N'} {e : N →ₗ[A] N'}
    (h : ∀ n, e (g n) = g' (e n)) (x : IndK k N φ) :
    IndK.map (k := k) e (IndK.map (k := k) g x) = IndK.map (k := k) g' (IndK.map (k := k) e x) :=
  LinearMap.congr_fun (show (Ind.map (φ := φ) e).comp (Ind.map g) =
      (Ind.map (φ := φ) g').comp (Ind.map e) from Ind.ext fun z n => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Ind.map_tmul, Ind.map_tmul, Ind.map_tmul,
      Ind.map_tmul, h]) x

end Comm

end InductionAlong

end Categorification
