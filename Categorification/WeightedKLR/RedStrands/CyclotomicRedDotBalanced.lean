/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicRedPullback
import Categorification.KLR.CyclotomicEF
import Categorification.WeightedKLR.RedStrands.CyclotomicRedDotIdeal

/-!
# Balancing the dotted red crossing against the old cyclotomic block

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.5, proof of Theorem 4.25 and (4.5). At positive old height, imposing the old
cyclotomic quotient on the module factor kills the old-strand relations that
survive multiplication of an affine relation by the last dot power. The balance
uses the right action of the old block on the induction bimodule.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra CyclotomicAction CategoryTheory InductionAlong Polynomial
open scoped TensorProduct

universe u v w

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
    (Q : I → I → MvPolynomial (Fin 2) k) {a b : I → Polynomial k}
    (hab : ∀ j, a j ∣ b j) (i : I) {β : Multiset I}

local notation "γ" => ((Singleton.singleton i : Multiset I) + β)
local notation "R" => KLRAlgebra k Q γ
local notation "mkB" => CycKLR.mk k Q b γ
local notation "φ" => lastEmb Q b i (β := β) rfl

/-- Cutting the old-strand relations at the last `i` gives a left linear combination of
embedded elements of the old cyclotomic ideal. The factorization uses the commuting images
of the two tensor factors. -/
private theorem cycL0_cut_mem_span (hβ : 0 < β.card) {z : R}
    (hz : z ∈ cycL0 a (zero_lt_card_single_add i β)) :
    z * cL Q i β 1 ∈ Submodule.span R (cL Q i β '' (cycIdeal Q a β : Set _)) := by
  let J := Submodule.span R (cL Q i β '' (cycIdeal Q a β : Set _))
  let p : KLRAlgebra k Q β := cycAt a ⟨0, hβ⟩
  have ht (t : KLRAlgebra k Q β ⊗[k] KLRAlgebra k Q {i}) : cL Q i β p * cLL Q i β t ∈ J := by
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, mul_add]; exact J.add_mem hx hy
    | tmul x y =>
      have fac : cL Q i β p * cLL Q i β (x ⊗ₜ y) = cLL Q i β (1 ⊗ₜ y) * cL Q i β (p * x) := by
        rw [← cLL_tmul_one, ← cLL_tmul_one, ← cLL_mul, ← cLL_mul]
        simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [fac]
      exact J.smul_mem _ (Submodule.subset_span ⟨_, TwoSidedIdeal.mul_mem_right _ _ _ (cycAt_mem_cycIdeal a hβ), rfl⟩)
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨t, he⟩ := exists_cLL_of_subR0 i β hw
    rw [mul_assoc, he, ← cL_one_mul_cLL i β t, ← mul_assoc, cycAt_mul_cL_one i β a hβ, cLL_tmul_one]
    exact ht t
  | zero => rw [zero_mul]; exact J.zero_mem
  | add x y _ _ hx hy => rw [add_mul]; exact J.add_mem hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact J.smul_mem _ hx

private theorem mk_cL_eq_lastEmb (y : KLRAlgebra k Q β) :
    mkB (cL Q i β y) = φ (CycKLR.mk k Q b β y) := by
  rw [lastEmb_mk, lastIncl_apply, castKLR_rfl]

variable (M : ModuleCat.{max u v w} (CycKLR k Q a β))

private abbrev pullModule := (cyclotomicRedPullback.{u,v,w} Q hab β).obj M
local notation "pulled" => pullModule Q hab M
local notation "gen" => Ind.tmul (N := pulled) (unitGen φ)

set_option backward.isDefEq.respectTransparency false in
private theorem cut_smul_gen (z : R) (n : M) :
    mkB (z * cL Q i β 1) • gen n = mkB z • gen n := by
  rw [map_mul, mul_smul, mk_cL_eq_lastEmb, map_one, Ind.smul_tmul]
  have he : φ 1 • unitGen φ = unitGen φ := Subtype.ext (unit_mul_unit φ)
  rw [he]

set_option backward.isDefEq.respectTransparency false in
/-- The old-strand cyclotomic relations kill the unit tensor after pulling an old-block
module through the red strand (Webster, arXiv:1309.3796v2, §4.5, proof of Theorem 4.25). -/
theorem cyclotomicRedCycL0_smul_tmul (hβ : 0 < β.card) {z : R}
    (hz : z ∈ cycL0 a (zero_lt_card_single_add i β)) (n : M) :
    mkB z • Ind.tmul (N := (cyclotomicRedPullback Q hab β).obj M) (unitGen φ) n = 0 := by
  rw [← cut_smul_gen Q hab i M z n]
  have h := cycL0_cut_mem_span Q i hβ hz
  generalize z * cL Q i β 1 = r at h ⊢
  induction h using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy, rfl⟩ := hz
    rw [mk_cL_eq_lastEmb, Ind.smul_tmul]
    let c := CycKLR.mk k Q b β y
    have hbal : φ c • unitGen φ = MulOpposite.op c • unitGen φ := by
      apply Subtype.ext
      change φ c * φ 1 = φ 1 * φ c
      rw [← map_mul, ← map_mul, one_mul, mul_one]
    rw [hbal, Ind.op_smul_tmul]
    have hm : @SMul.smul (CycKLR k Q b β) (↑pulled) _ c n = 0 := by
      change cyclotomicRedProjection Q hab β (CycKLR.mk k Q b β y) • n = (0 : M)
      rw [cyclotomicRedProjection_mk, (CycKLR.mk_eq_zero_iff y).mpr hy, zero_smul]
    exact (congrArg gen hm).trans (Ind.tmul_zero _)
  | zero => rw [map_zero, zero_smul]
  | add x y _ _ hx hy => rw [map_add, add_smul, hx, hy, zero_add]
  | smul r x _ hx => rw [smul_eq_mul, map_mul, mul_smul, hx, smul_zero]

set_option backward.isDefEq.respectTransparency false in
/-- At positive old height the extra dots kill the kernel of the cyclotomic projection on
an induced tensor with coefficients in the smaller block (Webster, arXiv:1309.3796v2,
§4.5, proof of Theorem 4.25). The old-strand part vanishes by balancing and the other
part already vanishes in the larger cyclotomic algebra. -/
theorem cyclotomicRedDotKernel_pos (hβ : 0 < β.card) (d : ℕ) (hi : b i = X ^ d * a i)
    (M : ModuleCat.{max u v w} (CycKLR k Q a β)) (x : CycKLR k Q b γ)
    (hx : cyclotomicRedProjection Q hab γ x = 0) (n : M) :
    Ind.tmul (N := (cyclotomicRedPullback Q hab β).obj M)
      ((x * dotElt Q b i (β := β) rfl ^ d) • unitGen φ) n = 0 := by
  let g := Ind.tmul (N := pullModule Q hab M) (unitGen φ) n
  obtain ⟨z, rfl⟩ := CycKLR.mk_surjective x
  rw [cyclotomicRedProjection_mk] at hx
  have h := redDot_cycIdeal_cut i β a b d hi ((CycKLR.mk_eq_zero_iff _).mp hx)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp h
  let y : R := z * KLRAlgebra.x ⟨β.card, lastPos_lt i β⟩ ^ d
  have hcut : mkB y • g = mkB (u + v) • g := by
    rw [cut_smul_gen Q hab i M y n |>.symm, huv]
  rw [← Ind.smul_tmul]
  change (mkB z * mkB (KLRAlgebra.x ⟨β.card, lastPos_lt i β⟩) ^ d) • g = 0
  rw [← map_pow, ← map_mul]
  change mkB y • g = 0
  rw [hcut, map_add, add_smul, cyclotomicRedCycL0_smul_tmul Q hab i M hβ hu n,
    (CycKLR.mk_eq_zero_iff _).mpr hv, zero_smul, zero_add]

end Categorification.Stendhal
