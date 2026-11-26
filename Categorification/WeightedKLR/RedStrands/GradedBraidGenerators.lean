/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorBraidingUnique
import Categorification.WeightedKLR.RedStrands.IteratedStandardCharacter

/-!
# Word tensors determine `F`-linear maps out of the ordered tensor product

Part of the proof of Webster, arXiv:1309.3796v2, §6.1, Corollary 6.10. For `n + 2 + m` factors,
two linear maps out of the ordered tensor product which commute with every `F_i` are equal if
they agree on the word tensors `F_{u_1} v_{λ_1} ⊗ ⋯ ⊗ F_{u_{n+2+m}} v_{λ_{n+2+m}}` with
`u_{n+2}` empty (`ext_tensorSpace_wordTensor`). This refines `ext_tensorSpace`, since every
`V^w` is spanned by the ordinary lowering words on its highest weight vector.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop

/-- A multilinear map vanishing on all tuples from given sets vanishes on all tuples from their
spans. -/
theorem multilinearMap_eq_zero_of_mem_span {R ι : Type*} [CommSemiring R] [Fintype ι]
    [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    {N : Type*} [AddCommMonoid N] [Module R N] (Φ : MultilinearMap R M N) (S : ∀ i, Set (M i))
    (h : ∀ y : ∀ i, M i, (∀ i, y i ∈ S i) → Φ y = 0) (x : ∀ i, M i)
    (hx : ∀ i, x i ∈ Submodule.span R (S i)) : Φ x = 0 := by
  suffices key : ∀ T : Finset ι, ∀ x : ∀ i, M i, (∀ i ∈ T, x i ∈ Submodule.span R (S i)) →
      (∀ i ∉ T, x i ∈ S i) → Φ x = 0 from
    key Finset.univ x (fun i _ => hx i) (fun i hi => absurd (Finset.mem_univ i) hi)
  intro T
  induction T using Finset.induction_on with
  | empty => exact fun x _ hS => h x fun i => hS i (Finset.notMem_empty i)
  | insert a T ha ih =>
    intro x hT hS
    suffices hz : ∀ z ∈ Submodule.span R (S a), Φ (Function.update x a z) = 0 by
      simpa using hz (x a) (hT a (Finset.mem_insert_self a T))
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      refine ih _ (fun i hi => ?_) (fun i hi => ?_)
      · rw [Function.update_of_ne (fun he : i = a => ha (he ▸ hi))]
        exact hT i (Finset.mem_insert_of_mem hi)
      · by_cases hia : i = a
        · subst hia
          simpa using hz
        · rw [Function.update_of_ne hia]
          exact hS i (by simp [hia, hi])
    | zero => exact Φ.map_update_zero x a
    | add y z _ _ hy hz => rw [Φ.map_update_add, hy, hz, add_zero]
    | smul c y _ hy => rw [Φ.map_update_smul, hy, smul_zero]

variable {I : Type} [DecidableEq I] (C : QuantumGroup.CartanDatum I)
  {Y : Type*} [AddCommGroup Y] {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular)

local notation "𝕂" => RatFunc ℚ
local notation "v" => (RatFunc.X : 𝕂)
local instance gradedBraidGeneratorsInst1 : NeZero v := ⟨RatFunc.X_ne_zero⟩

theorem ordinarySuffixOp_wordVec (w : Dom R) : ∀ (s l : List I),
    ordinarySuffixOp (fun i => Algebra.lsmul 𝕂 𝕂 (IrreducibleModule R v w.1) (F R v i)) s
      (wordVec w l) = wordVec w (s.reverse ++ l)
  | [], l => rfl
  | i :: s, l => by
    change ordinarySuffixOp _ s (F R v i • wordVec w l) = _
    rw [← wordVec_cons, ordinarySuffixOp_wordVec w s (i :: l)]
    simp

/-- `V^w` is spanned by the ordinary lowering words on its highest weight vector. -/
theorem span_ordinarySuffixOp (w : Dom R) :
    Submodule.span 𝕂 (Set.range fun l : List I =>
      ordinarySuffixOp (fun i => Algebra.lsmul 𝕂 𝕂 (IrreducibleModule R v w.1) (F R v i)) l
        (IrreducibleModule.hwv R v w.1)) = ⊤ := by
  rw [eq_top_iff, ← span_wordVec w]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨l, rfl⟩
  refine Submodule.subset_span ⟨l.reverse, ?_⟩
  change _ = wordVec w l
  rw [← wordVec_nil]
  exact (ordinarySuffixOp_wordVec C w l.reverse []).trans (by simp)

include hR in
/-- **Word tensors with an empty word at `n + 2` determine `F`-linear maps** (Webster,
arXiv:1309.3796v2, proof of Corollary 6.10): two linear maps out of the ordered tensor product
of `n + 2 + m` factors which commute with every `F_i` are equal if they agree on every word
tensor `F_{u_1} v_{λ_1} ⊗ ⋯ ⊗ F_{u_{n+2+m}} v_{λ_{n+2+m}}` with `u_{n+2}` empty. -/
theorem ext_tensorSpace_wordTensor {n m : ℕ} (wt : Fin (n + 2 + m) → Dom R) {N : Type*}
    [AddCommGroup N] [Module 𝕂 N]
    (actN : LieLean.QuantumGroup R v →ₐ[𝕂] Module.End 𝕂 N) (f g : TensorSpace wt →ₗ[𝕂] N)
    (hf : ∀ (i : I) (z : TensorSpace wt),
      f (tensorRepresentation wt (F R v i) z) = actN (F R v i) (f z))
    (hg : ∀ (i : I) (z : TensorSpace wt),
      g (tensorRepresentation wt (F R v i) z) = actN (F R v i) (g z))
    (h : ∀ u : Fin (n + 2 + m) → List I, u (Fin.castAdd m (Fin.natAdd n 1)) = [] →
      f (wordTensor C wt u) = g (wordTensor C wt u)) :
    f = g := by
  refine ext_tensorSpace hR wt actN f g hf hg fun x _ hx => sub_eq_zero.1 ?_
  let S : ∀ j, Set (IrreducibleModule R v (wt j).1) := fun j =>
    {y | ∃ l : List I, (j = Fin.castAdd m (Fin.natAdd n 1) → l = []) ∧
      y = ordinarySuffixOp (fun i => Algebra.lsmul 𝕂 𝕂 (IrreducibleModule R v (wt j).1)
        (F R v i)) l (IrreducibleModule.hwv R v (wt j).1)}
  change ((f - g).compMultilinearMap (PiTensorProduct.tprod 𝕂)) x = 0
  refine multilinearMap_eq_zero_of_mem_span _ S (fun y hy => ?_) x fun j => ?_
  · choose u hu using hy
    have hy' : y = fun j => ordinarySuffixOp (fun i => Algebra.lsmul 𝕂 𝕂
        (IrreducibleModule R v (wt j).1) (F R v i)) (u j) (IrreducibleModule.hwv R v (wt j).1) :=
      funext fun j => (hu j).2
    rw [LinearMap.compMultilinearMap_apply, LinearMap.sub_apply, sub_eq_zero, hy']
    exact h u ((hu _).1 rfl)
  · by_cases hj : j = Fin.castAdd m (Fin.natAdd n 1)
    · subst hj
      exact Submodule.subset_span ⟨[], fun _ => rfl, hx⟩
    · have hsub : (Set.range fun l : List I => ordinarySuffixOp (fun i => Algebra.lsmul 𝕂 𝕂
          (IrreducibleModule R v (wt j).1) (F R v i)) l (IrreducibleModule.hwv R v (wt j).1)) ⊆
            S j := by
        rintro _ ⟨l, rfl⟩
        exact ⟨l, fun h => absurd h hj, rfl⟩
      refine Submodule.span_mono hsub ?_
      rw [span_ordinarySuffixOp C (wt j)]
      exact Submodule.mem_top

end Categorification.Stendhal.FirstWeight
