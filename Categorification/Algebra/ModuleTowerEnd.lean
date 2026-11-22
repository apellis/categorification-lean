/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ModuleTowerK0
import Categorification.Algebra.ModuleCatLinear
import Categorification.CategoryTheory.PiAbelian

/-!
# Endomorphisms of simple objects of `FGTower A`

For a tower of `k`-algebras `A 0, A 1, …`, if every endomorphism of a simple module at every
level is a scalar from `k`, then every simple object `S` of `FGTower A` has `End(S) = k`
(`ModuleTower.finrank_end_simple`). This is the condition `End(S) = k` of Chuang–Rouquier,
arXiv:math/0407205v2, §5.2.1, for the category of finitely generated modules along an
`i`-string of Webster's tensor product algebras (arXiv:1309.3796v2, §5).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.ModuleTower

open CategoryTheory Limits Module

universe u

variable {A : ℕ → Type u} [∀ m, Ring (A m)] [∀ m, IsNoetherianRing (A m)]
  (k : Type u) [Field k] [∀ m, Algebra k (A m)]

/-- **`End(S) = k` for a simple object of `FGTower A`**, from the corresponding property of the
simple modules at each level. -/
theorem finrank_end_simple
    (h : ∀ m (M : ModuleCat.{u} (A m)), IsSimpleModule (A m) M → ∀ f : M ⟶ M,
      ∃ c : k, ∀ v, f.hom v = algebraMap k (A m) c • v)
    (S : FGTower A) [Simple S] : finrank k (S ⟶ S) = 1 := by
  refine (finrank_eq_one_iff_of_nonzero' (𝟙 S) (id_nonzero S)).mpr fun w => ?_
  obtain ⟨c, hc⟩ := h (level S) (S.obj (level S)) (isSimpleModule_level S) (w.hom (level S))
  refine ⟨c, ObjectProperty.hom_ext _ (funext fun n => ?_)⟩
  by_cases hn : n = level S
  · subst hn
    refine ModuleCat.hom_ext (LinearMap.ext fun v => ?_)
    exact (hc v).symm
  · exact (isZero_of_ne_level S hn).eq_of_src _ _

end Categorification.ModuleTower
