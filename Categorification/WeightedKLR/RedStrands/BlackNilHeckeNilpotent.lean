/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackNilHeckeTower
import Categorification.WeightedKLR.RedStrands.TensorFinite

/-!
# The dot on the appended black strand is nilpotent

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §5.1. The dot
`y = x_n · ν_i(1)` on the newest black strand in `T^λ` (`appendedDot`) is nilpotent: the dots
of `T^λ` are nilpotent (Definitions 4.6–4.7, `tensorProjection_dot_nilpotent`), and `y` is a dot
times an idempotent commuting with it (`isNilpotent_appendedDot`). Along a tower of rings in
which the dots vanish from some level on, the action of the dots on restriction is nilpotent
with a uniform exponent (`resTowerX_pow_eq_zero`); this is the nilpotence hypothesis in
Chuang–Rouquier's study of `𝔰𝔩₂`-categorifications (arXiv:math/0407205v2, §5.2.1).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.InductionAlong

open CategoryTheory

universe u

variable {B : ℕ → Type u} [∀ m, Ring (B m)] (φ : ∀ m, B m →ₙ+* B (m + 1))

theorem resTowerX_pow_app_val (y : ∀ m, B (m + 1)) (hy : ∀ m a, y m * φ m a = φ m a * y m)
    (N : ℕ) (M : ∀ m, ModuleCat.{u} (B m)) (m : ℕ) (r) :
    ((((resTowerX φ y hy) ^ N).app M m).hom r).val = y m ^ N • r.val := by
  induction N generalizing r with
  | zero => simp only [pow_zero, one_smul]; rfl
  | succ N ih =>
    rw [pow_succ, resTower_mul_app]
    refine (ih _).trans ?_
    rw [pow_succ, mul_smul]
    rfl

theorem resTowerX_pow_eq_zero (y : ∀ m, B (m + 1)) (hy : ∀ m a, y m * φ m a = φ m a * y m)
    {N : ℕ} (hN : ∀ m, y m ^ N = 0) : resTowerX φ y hy ^ N = 0 :=
  resTower_ext fun M m r => Res.ext (by
    rw [resTowerX_pow_app_val, hN, zero_smul]
    rfl)

/-- A family of nilpotent elements of rings which are zero from some index on has a uniform
nilpotency exponent. -/
theorem exists_pow_eq_zero_of_subsingleton {R : ℕ → Type*} [∀ m, Ring (R m)] (y : ∀ m, R m)
    (hy : ∀ m, IsNilpotent (y m)) (hB : ∃ B, ∀ m, B ≤ m → Subsingleton (R m)) :
    ∃ N, ∀ m, y m ^ N = 0 := by
  classical
  obtain ⟨B, hB⟩ := hB
  choose n hn using hy
  refine ⟨(Finset.range B).sup n, fun m => ?_⟩
  by_cases hm : B ≤ m
  · have := hB m hm
    exact Subsingleton.elim _ _
  · have hle : n m ≤ (Finset.range B).sup n :=
      Finset.le_sup (Finset.mem_range.mpr (not_le.mp hm))
    rw [← Nat.sub_add_cancel hle, pow_add, hn, mul_zero]

end Categorification.InductionAlong

namespace Categorification.Stendhal

open StendhalAlgebraAllOrders

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type u} {ℓ : ℕ} [DecidableEq I] {k : Type u} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν : Multiset I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "G" => appendBlackValue Q Λ i ν
local notation "P" => redOrderedIdem k Q Λ ν
local notation "P'" => redOrderedIdem k Q Λ νᵢ
local notation "π'" => TensorProductAlgebra.mk Q Λ νᵢ

theorem newDot_mul_redOrderedIdem_mem : newDot Q Λ i ν * P' ∈ Subsemigroup.corner P' :=
  (orderProjection Q Λ νᵢ (newDot Q Λ i ν)).2

/-- The dot on the newest black strand is a dot of `T^λ` times the idempotent `ν_i(1)`. -/
theorem appendedDot_eq_mul :
    appendedDot Q Λ i ν = π' ⟨newDot Q Λ i ν * P', newDot_mul_redOrderedIdem_mem Q Λ i ν⟩ *
      π' ⟨G P, E1_mem Q Λ i ν⟩ := by
  rw [appendedDot, tensorProductAlgebra_mk_mul]
  refine tensorProductAlgebra_mk_eq Q Λ _ _ ?_
  rw [mul_assoc, ((Subsemigroup.mem_corner_iff isIdempotentElem_redOrderedIdem).mp
    (E1_mem Q Λ i ν)).1]

theorem commute_appendedDot_factors :
    Commute (π' ⟨newDot Q Λ i ν * P', newDot_mul_redOrderedIdem_mem Q Λ i ν⟩)
      (π' ⟨G P, E1_mem Q Λ i ν⟩) := by
  have hE := (Subsemigroup.mem_corner_iff isIdempotentElem_redOrderedIdem).mp (E1_mem Q Λ i ν)
  change _ * _ = _ * _
  rw [tensorProductAlgebra_mk_mul, tensorProductAlgebra_mk_mul]
  refine tensorProductAlgebra_mk_eq Q Λ _ _ ?_
  rw [mul_assoc, hE.1, ← mul_assoc, ← (newDot_commute Q Λ i ν P).eq, mul_assoc, hE.2]

variable {C : QuantumGroup.CartanDatum I} (hQ : KLR.IsRouquierQ C Q)

include hQ in
/-- **The dot on the newest black strand is nilpotent** in Webster's tensor product algebra
(arXiv:1309.3796v2, Definitions 4.6–4.7 and §5.1). -/
theorem isNilpotent_appendedDot : IsNilpotent (appendedDot Q Λ i ν) := by
  rw [appendedDot_eq_mul]
  refine (commute_appendedDot_factors Q Λ i ν).isNilpotent_mul_right ?_
  have h := tensorProjection_dot_nilpotent (Q := Q) Λ νᵢ hQ
    ⟨Multiset.card (stendhalWeight ℓ ν), by rw [card_stendhalWeight_addBlack]; omega⟩
  convert h using 1
  change _ = TensorProductAlgebra.mk Q Λ νᵢ
    (orderProjection Q Λ νᵢ (affineCover Q Λ νᵢ (KLR.KLRAlgebra.x _)))
  rw [affineCover_x]
  rfl

end Categorification.Stendhal
