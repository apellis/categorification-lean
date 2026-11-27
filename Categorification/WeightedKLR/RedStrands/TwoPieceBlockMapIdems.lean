/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceBlockMaps
import Categorification.KLR.Crystal.IndDecomp
import Categorification.KLR.BarK0
import Categorification.KLR.ReindexSymmetries

/-!
# The prefix map between two-piece idempotents

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1,
proof of Proposition 5.5. For loadings `t, t'` of the first `ℓ` red strands and black words
`u, u'` of the last block, `e(t λ u) ι(a) e(t' λ u')` vanishes unless `u = u'`, and is then the
concatenation of `e(t) a e(t')` with `e(λ u)` (`e_mul_prefixBlockMap_mul_e`); the same element
is obtained by multiplying `ι(e(t) a ⊗ 1)` on the right by `e(t' λ u')`
(`concat_tmul_one_mul_e`). The prefix map commutes with the horizontal flip
(`hflip_prefixBlockMap`).
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (θ β : Multiset I)

local notation "lc" => Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)
local notation "S" => stendhalQ Q Λ
local notation "S'" => stendhalQ Q (Λ ∘ Fin.castSucc)
local notation "ρ" => redSubfamilyRelabel Q Λ Fin.castSucc (Fin.castSucc_injective ℓ) θ
local notation "A" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" => Multiset.map lc (stendhalWeight 1 β)
local notation "H" => parabolicInputWeights_add (ℓ := ℓ) θ β

omit [DecidableEq I] in
theorem hflip_castKLR' {J : Type*} [DecidableEq J] {Q' : J → J → MvPolynomial (Fin 2) k}
    {μ μ' : Multiset J} (h : μ = μ') (r : KLRAlgebra k Q' μ) :
    hflip (castKLR Q' h r) = castKLR Q' h (hflip r) := by
  subst h; rfl

/-- `e(t λ_{ℓ+1} u) = ι(e(t) ⊗ e(λ_{ℓ+1} u))`. -/
theorem e_twoPieceLoading (t : Seq (stendhalWeight ℓ θ)) (u : Seq β) :
    (e (twoPieceLoading θ β t u) : KLRAlgebra k S (stendhalWeight (ℓ + 1) (θ + β))) =
      castKLR S H (concat S A δ (relabelEquiv ρ (e t) ⊗ₜ
        e (Seq.map lc (SingleRed.insertWord β u)))) := by
  rw [relabelEquiv_apply, relabelHom_e, concat_e_tmul_e, castKLR_e]
  rfl

theorem e_mul_lastWordIdem_mul_e (u u' : Seq β) :
    (e (Seq.map lc (SingleRed.insertWord β u)) * lastWordIdem Q Λ β *
      e (Seq.map lc (SingleRed.insertWord β u')) : KLRAlgebra k S δ) =
      if u = u' then e (Seq.map lc (SingleRed.insertWord β u)) else 0 := by
  rw [lastWordIdem, e_mul_eSum, ite_eq_left_of_eq_true _ _
    (eq_true (show _ ∈ lastWords β from Finset.mem_image_of_mem _ (Finset.mem_univ u))), e_mul_e]
  by_cases h : u = u'
  · subst h; simp
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h' => h (lastWord_injective β h')),
      ite_eq_right_of_eq_false _ _ (eq_false h)]

/-- **The prefix map between two-piece idempotents**:
`e(t λ u) ι(a) e(t' λ u') = δ_{u u'} ι(e(t) a e(t') ⊗ e(λ u))`. -/
theorem e_mul_prefixBlockMap_mul_e (t t' : Seq (stendhalWeight ℓ θ)) (u u' : Seq β)
    (a : KLRAlgebra k S' (stendhalWeight ℓ θ)) :
    e (twoPieceLoading θ β t u) * prefixBlockMap Q Λ θ β a * e (twoPieceLoading θ β t' u') =
      if u = u' then
        castKLR S H (concat S A δ (relabelEquiv ρ (e t * a * e t') ⊗ₜ
          e (Seq.map lc (SingleRed.insertWord β u))))
      else 0 := by
  rw [e_twoPieceLoading, e_twoPieceLoading, prefixBlockMap_apply, ← map_mul, ← map_mul,
    ← concat_mul, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, ← map_mul, ← map_mul, e_mul_lastWordIdem_mul_e]
  split_ifs
  · rfl
  · rw [TensorProduct.tmul_zero, map_zero, map_zero]

/-- `ι(e(t) a ⊗ 1) e(t' λ u') = ι(e(t) a e(t') ⊗ e(λ u'))`. -/
theorem concat_tmul_one_mul_e (t' : Seq (stendhalWeight ℓ θ)) (u' : Seq β)
    (a : KLRAlgebra k S' (stendhalWeight ℓ θ)) :
    castKLR S H (concat S A δ (relabelEquiv ρ a ⊗ₜ 1)) * e (twoPieceLoading θ β t' u') =
      castKLR S H (concat S A δ (relabelEquiv ρ (a * e t') ⊗ₜ
        e (Seq.map lc (SingleRed.insertWord β u')))) := by
  rw [e_twoPieceLoading, ← map_mul, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    ← map_mul]

/-- The prefix map commutes with the horizontal flip. -/
theorem hflip_prefixBlockMap (a : KLRAlgebra k S' (stendhalWeight ℓ θ)) :
    hflip (prefixBlockMap Q Λ θ β a) = prefixBlockMap Q Λ θ β (hflip a) := by
  rw [prefixBlockMap_apply, prefixBlockMap_apply, hflip_castKLR', hflip_concat_tmul_tmul,
    relabelEquiv_apply, relabelEquiv_apply, hflip_relabelHom, lastWordIdem, hflip_eSum]

end Categorification.Stendhal
