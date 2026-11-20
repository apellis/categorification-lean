/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Order.Atoms

/-!
# A unique simple quotient from a simple idempotent truncation

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.2,
Lemma 5.9. Let `e` be an idempotent of a ring `R` and `M` an `R`-module. If `eM` is simple
over `eRe` (every nonzero element of `eM` generates `eM` over `eRe`) and `eM` generates `M`,
then `M` has a unique maximal submodule, so a unique simple quotient.

Webster states the lemma for right modules; a right module is a left module over the opposite
ring, so the statement here, for left modules, covers it.

## Main results

* `existsUnique_isCoatom_of_idempotent`: Lemma 5.9.
-/

namespace Categorification

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- **Webster, arXiv:1309.3796v3, Lemma 5.9**: if `eM ≠ 0` is simple over `eRe` and generates
`M`, then `M` has a unique maximal submodule. -/
theorem existsUnique_isCoatom_of_idempotent {e : R} (he : IsIdempotentElem e)
    (hne : ∃ x : M, e • x = x ∧ x ≠ 0)
    (hsimple : ∀ x y : M, e • x = x → e • y = y → x ≠ 0 → ∃ r : R, y = (e * r * e) • x)
    (hgen : Submodule.span R {x : M | e • x = x} = ⊤) :
    ∃! N : Submodule R M, IsCoatom N := by
  -- A proper submodule is killed by `e`.
  have hkill : ∀ N : Submodule R M, N ≠ ⊤ → ∀ m ∈ N, e • m = 0 := by
    intro N hN m hm
    by_contra hx
    apply hN
    rw [eq_top_iff, ← hgen, Submodule.span_le]
    intro y hy
    have hex : e • (e • m) = e • m := by rw [smul_smul, he.eq]
    obtain ⟨r, rfl⟩ := hsimple _ y hex hy hx
    exact N.smul_mem _ (N.smul_mem e hm)
  -- The submodule of elements all of whose translates are killed by `e`.
  let K : Submodule R M :=
    { carrier := {m | ∀ r : R, e • r • m = 0}
      add_mem' := fun ha hb r => by rw [smul_add, smul_add, ha r, hb r, add_zero]
      zero_mem' := fun r => by rw [smul_zero, smul_zero]
      smul_mem' := fun c m hm r => by rw [smul_smul r c]; exact hm (r * c) }
  obtain ⟨x, hx, hx0⟩ := hne
  have hK : K ≠ ⊤ := by
    intro h
    have : x ∈ K := h ▸ Submodule.mem_top
    exact hx0 (by simpa [hx] using this 1)
  let N₀ := sSup {N : Submodule R M | N ≠ ⊤}
  have hle : ∀ N : Submodule R M, N ≠ ⊤ → N ≤ N₀ := fun N hN => le_sSup hN
  have hN₀K : N₀ ≤ K := sSup_le fun N hN m hm r => hkill N hN _ (N.smul_mem r hm)
  have hN₀ : N₀ ≠ ⊤ := fun h => hK (eq_top_iff.2 (h ▸ hN₀K))
  have hco : IsCoatom N₀ := ⟨hN₀, fun N hN => by
    by_contra h
    exact (not_le_of_gt hN) (hle N h)⟩
  refine ⟨N₀, hco, fun N hN => ?_⟩
  exact (hN.le_iff.1 (hle N hN.1)).resolve_left hco.1 |>.symm

end Categorification
